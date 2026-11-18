------------------------------------------------------------------------
-- The repaired limit rules (notes/limits-representables.md §4.1):
--
--  R1  Specified shapes. The cone and cone-morphism contexts are given
--      by a fixed construction from the diagram context, not by the
--      permissive recognition judgment.
--        * coneC: Mikhail's Thm 3.3 construction, implemented here for
--          globular diagrams of dimension ≤ 2.
--        * morC: cone morphisms (ctrf, n = 1) between two copies of
--          the canonical cone, for diagrams of dimension ≤ 1, with the
--          comparison cell m_f : p_f ; (m_a ◁ f) ⇛ m_b ; q_f.
--      Both are checked, on examples, to pass the recognition rules
--      (cone rules, and the ctrf rules with both repairs).
--  R2  Certified comparison cells. In morC, the comparison cells over
--      positive-dimensional diagram variables are *marked*. A
--      substitution into a marked context must supply, for each marked
--      variable, a term carrying an invertibility certificate (`cert`).
--
-- Then the instance that drives the collapse argument (researcher,
-- notes/conjectures/catt-lim-pseudo-vs-gray.md §4) is checked: over the
-- diagram 1_Y, an arbitrary ambient 3-cell z : a ⇛ b gives a
-- well-typed cone morphism, so the unrestricted universal property
-- would apply to it; the repaired rule rejects it unless z itself is
-- certified.
--
-- `cert` is a syntactic, decidable certificate: marked variables,
-- full coherences, and operations all of whose top-dimensional
-- arguments are certified. Its semantic justification is that
-- coherences are invertible and composites and whiskerings of
-- invertible cells are invertible (Benjamin–Markakis, arXiv
-- 2406.12127); that is cited, not formalized here.
------------------------------------------------------------------------
module CaTTExp.Lim.Repaired where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Conditions
open import CaTTExp.Lim.Rules
open import CaTTExp.Lim.Terms
open import CaTTExp.Lim.Defects
  using (Γarr; Parr; Qarr; Marr; Γloop; Πcanonical; Πnoncanonical)

private
  v : Nat → Tm
  v = var

  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

------------------------------------------------------------------------
-- R1. The canonical cone (Mikhail Thm 3.3), dimension ≤ 2, with the
-- projection of x named `pn x`.
--   dim 0:  p_x : c → x
--   dim 1:  p_f : p_b ⇒ p_a · f                       (f : a → b)
--   dim 2:  p_α : p_g ⇛ p_f ; (p_a ▷ α)               (α : f ⇒ g)

projTy : (c : Name) (pn : Name → Name) (x : Name) → Ty → Maybe Ty
projTy c pn x ⋆ = just (c ⇒⋆ x)
projTy c pn x (arr ⋆ (var a) (var b)) =
  just (arr (c ⇒⋆ b) (v (pn b)) (comp (v c) (v a) (v (pn a)) (v b) (v x)))
projTy c pn x (arr (arr ⋆ (var a) (var b)) (var f) (var g)) =
  just (arr (arr (c ⇒⋆ b) (v (pn b)) pag) (v (pn g))
            (vcomp (v c) (v b) (v (pn b)) paf (v (pn f)) pag
                   (whL (v c) (v a) (v (pn a)) (v b) (v f) (v g) (v x))))
  where
  paf pag : Tm
  paf = comp (v c) (v a) (v (pn a)) (v b) (v f)
  pag = comp (v c) (v a) (v (pn a)) (v b) (v g)
projTy _ _ _ _ = nothing

coneWith : (c : Name) (pn : Name → Name) → NCtx → Maybe NCtx
coneWith c pn ∅           = just ∅
coneWith c pn (Γ ▹ x ∶ X) =
  coneWith c pn Γ >>= λ Π → projTy c pn x X >>= λ T → just (Π ▹ pn x ∶ T)

-- Naming scheme: apex c, then the i-th diagram variable gets p = c+1+i,
-- q = c+1+n+i, m = c+1+2n+i (n = |Γ|).
private
  idx : NCtx → Name → Nat
  idx Γ x with levelOf Γ x
  ... | just i  = i
  ... | nothing = 0

pName qName mName : NCtx → Name → Name → Name
pName Γ c x = suc c + idx Γ x
qName Γ c x = suc c + size Γ + idx Γ x
mName Γ c x = suc c + size Γ + size Γ + idx Γ x

coneC : NCtx → Name → Maybe NCtx
coneC Γ c = coneWith c (pName Γ c) Γ

-- The specified construction reproduces the canonical cones used above.
_ : coneC Γarr 3 ≡ just Parr
_ = refl

_ : coneC Γloop 3 ≡ just Πcanonical
_ = refl

-- The repaired cone judgment: the specified cone, which in addition
-- passes the recognition rules.
record SpecCone (Γ : NCtx) (c : Name) (Π : NCtx) : Set where
  constructor spec
  field
    isSpecified : coneC Γ c ≡ just Π
    recognised  : Cone Γ c Π

-- The non-canonical cone of Defects.D5 is not the specified one.
noncanonical-rejected : SpecCone Γloop 3 Πnoncanonical → ⊥
noncanonical-rejected (spec () _)

canonical-accepted : SpecCone Γloop 3 Πcanonical
canonical-accepted = spec refl (from-just (cone? Γloop 3 Πcanonical))

-- A 2-dimensional example: the diagram of Mikhail's Example 4.1,
-- x0 y1 f2 g3 α4 (α : f ⇒ g), apex 5.
Γ41 : NCtx
Γ41 = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (0 ⇒⋆ 1) ▹ 4 ∶ arr (0 ⇒⋆ 1) (v 2) (v 3)

cone41 : SpecCone Γ41 5 (from-just (coneC Γ41 5))
cone41 = spec refl (from-just (cone? _ _ _))

------------------------------------------------------------------------
-- R1. Cone morphisms between two copies of the canonical cone, for
-- diagrams of dimension ≤ 1, together with the marking.
--   m_x : p_x ⇒ q_x                                         (unmarked)
--   m_f : p_f ; (m_a ◁ f)  ⇛  m_b ; q_f      (f : a → b)     (marked)

record Shape : Set where
  constructor shape
  field
    M3     : NCtx
    marked : List Name

compTy : (Γ : NCtx) (c : Name) (x : Name) → Ty → Maybe (Ty × Bool)
compTy Γ c x ⋆ = just (arr (c ⇒⋆ x) (v (p x)) (v (q x)) , false)
  where p q : Name → Name
        p = pName Γ c
        q = qName Γ c
compTy Γ c f (arr ⋆ (var a) (var b)) =
  just (arr (arr (c ⇒⋆ b) (v (p b)) qaf)
            (vcomp (v c) (v b) (v (p b)) paf (v (p f)) qaf
                   (whR (v c) (v a) (v (p a)) (v (q a)) (v (m a)) (v b) (v f)))
            (vcomp (v c) (v b) (v (p b)) (v (q b)) (v (m b)) qaf (v (q f)))
       , true)
  where
  p q m : Name → Name
  p = pName Γ c
  q = qName Γ c
  m = mName Γ c
  paf qaf : Tm
  paf = comp (v c) (v a) (v (p a)) (v b) (v f)
  qaf = comp (v c) (v a) (v (q a)) (v b) (v f)
compTy _ _ _ _ = nothing

private
  morWith : (Γfull : NCtx) (c : Name) → NCtx → Maybe Shape
  morWith Γf c ∅           = just (shape ∅ [])
  morWith Γf c (Γ ▹ x ∶ X) =
    morWith Γf c Γ >>= λ { (shape M μ) →
    compTy Γf c x X >>= λ { (T , mk) →
    just (shape (M ▹ mName Γf c x ∶ T) (if mk then μ ++ (mName Γf c x ∷ []) else μ)) } }

morC : NCtx → Name → Maybe Shape
morC Γ c = morWith Γ c Γ

-- The second cone of the morphism is the canonical cone with q-names.
coneQ : NCtx → Name → Maybe NCtx
coneQ Γ c = coneWith c (qName Γ c) Γ

-- On the arrow diagram this is exactly the intended context of D1,
-- with m_f (12) marked and m_x, m_y not.
_ : coneQ Γarr 3 ≡ just Qarr
_ = refl

_ : morC Γarr 3 ≡ just (shape Marr (12 ∷ []))
_ = refl

-- and the ctrf rules with both repairs accept it.
open Ctrf
open CtrfCheck

morArr-recognised : Ctrf1 fixed Γarr 3 Parr Qarr Marr
morArr-recognised = from-just (ctrf? fixed _ _ _ _ _)

-- A second example: a composable pair x0 y1 f2 z3 g4, apex 5.
Γpair : NCtx
Γpair = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ ⋆ ▹ 4 ∶ (1 ⇒⋆ 3)

morPair-recognised :
  Ctrf1 fixed Γpair 5 (from-just (coneC Γpair 5)) (from-just (coneQ Γpair 5))
                      (Shape.M3 (from-just (morC Γpair 5)))
morPair-recognised = from-just (ctrf? fixed _ _ _ _ _)

_ : Shape.marked (from-just (morC Γpair 5)) ≡ (18 ∷ 20 ∷ [])
_ = refl

------------------------------------------------------------------------
-- R2. Certificates and marked substitutions.

mutual
  cert : List Name → Tm → Bool
  cert μ (var n)               = elem n μ
  cert μ (coh Δ ⋆ γ)           = false
  cert μ (coh Δ (arr A t u) γ) =
    isCoh Δ A t u ∨
    (isOp Δ A t u ∧ (suc (dim A) ==ℕ dimCtx Δ) ∧ certTop μ (dimCtx Δ) Δ γ)
  cert μ (cst ())

  -- every argument substituted for a top-dimensional variable of Δ
  certTop : List Name → Nat → Ctx → Sub → Bool
  certTop μ d (Δ ▸ B) (γ ,ₛ t) = (if dim B ==ℕ d then cert μ t else true) ∧ certTop μ d Δ γ
  certTop μ d _       _        = true

certAt : List Name → NCtx → Sub → Name → Bool
certAt μ M θ m with termFor M θ m
... | just t  = cert μ t
... | nothing = false

-- θ : Ω → M is admissible for the repaired rules when it is well typed
-- and certifies every marked variable of M (μΩ: the certified
-- variables of Ω).
record CertSub (Ω : NCtx) (μΩ : List Name) (θ : Sub) (M : NCtx) (μM : List Name) : Set where
  constructor certsub
  field
    typed : SubOK Ω θ M
    certs : T (all (certAt μΩ M θ) μM)

------------------------------------------------------------------------
-- The collapse instance.
--
-- Ambient context Ω:  c20 Y21  r22 s23 : c → Y  a24 b25 : r ⇒ s  z26 : a ⇛ b.
-- Diagram: the arrow f : x → y, substituted by x, y ↦ Y and f ↦ 1_Y.
-- Cones P, Q with both legs r (resp. s) and comparison the inverse
-- right unitor; vertex comparisons m_x = a, m_y = b; and
--   m_f ↦ Z = (naturality of ρ⁻¹ at a) ; (z ◁₁ ρ⁻¹_s)
--          : ρ⁻¹_r ; (a ◁ 1_Y)  ⇛  b ; ρ⁻¹_s.
-- Z is invertible iff z is (researcher §4); the unrestricted universal
-- property would make every such m_f invertible.

Ω : NCtx
Ω = ∅ ▹ 20 ∶ ⋆ ▹ 21 ∶ ⋆ ▹ 22 ∶ (20 ⇒⋆ 21) ▹ 23 ∶ (20 ⇒⋆ 21)
      ▹ 24 ∶ arr (20 ⇒⋆ 21) (v 22) (v 23) ▹ 25 ∶ arr (20 ⇒⋆ 21) (v 22) (v 23)
      ▹ 26 ∶ arr (arr (20 ⇒⋆ 21) (v 22) (v 23)) (v 24) (v 25)

private
  c Y r s a b z : Tm
  c = v 20 ; Y = v 21 ; r = v 22 ; s = v 23 ; a = v 24 ; b = v 25 ; z = v 26

  1Y r1 s1 ρr ρs : Tm
  1Y = idc Y
  r1 = comp c Y r Y 1Y
  s1 = comp c Y s Y 1Y
  ρr = runitInv c Y r
  ρs = runitInv c Y s

  Src Mid Tgt : Tm
  Src = vcomp c Y r r1 ρr s1 (whR c Y r s a Y 1Y)
  Mid = vcomp c Y r s a s1 ρs
  Tgt = vcomp c Y r s b s1 ρs

  Z : Tm
  Z = vcomp₃ c Y r s1 Src Mid (runitNat c Y r s a) Tgt (wh₃ c Y r s a b z s1 ρs)

-- The cone-morphism context over the arrow (full context) and θ.
Mfull : NCtx
Mfull = ctrfCtx Γarr 3 Parr Qarr Marr

θ : Sub
θ = ⟪ Y ∷ Y ∷ 1Y ∷ c ∷ r ∷ r ∷ ρr ∷ s ∷ s ∷ ρs ∷ a ∷ b ∷ Z ∷ [] ⟫

-- In the intended (unmarked) calculus this is a legitimate cone
-- morphism: θ is a well-typed substitution into the cone-morphism
-- context, built from an arbitrary 3-cell z.
collapse-instance-typed : SubOK Ω θ Mfull
collapse-instance-typed = from-just (sub? Ω θ Mfull)

-- The repaired rule rejects it: m_f is marked and Z is not certified
-- when z is an ordinary (uncertified) variable.
collapse-instance-rejected : CertSub Ω [] θ Mfull (12 ∷ []) → ⊥
collapse-instance-rejected (certsub _ ())

-- It is accepted exactly when z is itself certified, so the repair does
-- not reject invertible comparisons.
collapse-instance-if-z-certified : CertSub Ω (26 ∷ []) θ Mfull (12 ∷ [])
collapse-instance-if-z-certified = certsub collapse-instance-typed tt
