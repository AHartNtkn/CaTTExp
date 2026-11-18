------------------------------------------------------------------------
-- Machine-checked defects of the printed rules of CaTT_lim
-- (Mikhail, arXiv 2412.13310v2, Def. 4.15).
--
--  D1  The printed ctrf rule admits no cone morphism over an arrow whose
--      comparison cell m_f has the intended boundary (any 2-cell type
--      mentioning q_x, e.g. p_y ⇒ q_x f), whatever its source and
--      target terms are, and whatever type the duplicate q_f is given.
--      Cause: the source condition selects earlier connecting cells p
--      through τ(p); the intended source p_f ; (m_x ◁ f) needs m_x,
--      which is only reachable through σ(m_x) = p_x.
--  D2  "x′ : X" copies the type verbatim, so the duplicated block is not
--      a second cone: no printed derivation has q_f : q_y ⇒ q_x f.
--  D3  The same selector defect in the printed gray rule rejects the
--      paper's own Example 4.1 component p_f : f·p_y ⇒ p_x·f′, and
--      every component over an arrow whose type mentions y′.
--  D4  What the printed rules do accept over an arrow is degenerate:
--      p_f : f ⇒ f′ with f′ : x → y, and m_f : p_f ⇛ q_f with q_f a
--      parallel copy of p_f.
--  D5  The cone judgment admits a non-canonical cone over
--      (x, f : x → x, α : f ⇒ f): its α-projection has source
--      r ; (r ◁ f), using r twice. The canonical cone (Thm 3.3) is also
--      admitted. That the two have non-equivalent constant-diagram
--      instances is the verified researcher result in
--      notes/conjectures/lax-colimit-of-point.md; it is not re-proved
--      here.
--
-- With both repairs (`fixed` in Rules.agda) the intended contexts of
-- D1–D3 are accepted (checked below).
------------------------------------------------------------------------
module CaTTExp.Lim.Defects where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Conditions
open import CaTTExp.Lim.Rules
open import CaTTExp.Lim.Terms

private
  v : Nat → Tm
  v = var

  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

  -- f · g for 1-cells given by names (x —f→ y —g→ z)
  c₁ : Nat → Nat → Nat → Nat → Nat → Tm
  c₁ x y f z g = comp (v x) (v y) (v f) (v z) (v g)

------------------------------------------------------------------------
-- The arrow diagram and the intended cone morphism.
--   x0 y1 f2 | c3 | p_x4 p_y5 p_f6 | q_x7 q_y8 q_f9 | m_x10 m_y11 m_f12

Γarr : NCtx
Γarr = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1)

-- The canonical cone P (Thm 3.3): p_f : p_y ⇒ p_x · f.
Parr : NCtx
Parr = ∅ ▹ 4 ∶ (3 ⇒⋆ 0) ▹ 5 ∶ (3 ⇒⋆ 1) ▹ 6 ∶ arr (3 ⇒⋆ 1) (v 5) (c₁ 3 0 4 1 2)

-- The intended second cone Q.
Qpre : NCtx
Qpre = ∅ ▹ 7 ∶ (3 ⇒⋆ 0) ▹ 8 ∶ (3 ⇒⋆ 1)

qfTy : Ty
qfTy = arr (3 ⇒⋆ 1) (v 8) (c₁ 3 0 7 1 2)

Qarr : NCtx
Qarr = Qpre ▹ 9 ∶ qfTy

-- Vertex comparisons m_x : p_x ⇒ q_x, m_y : p_y ⇒ q_y.
Mpre : NCtx
Mpre = ∅ ▹ 10 ∶ arr (3 ⇒⋆ 0) (v 4) (v 7) ▹ 11 ∶ arr (3 ⇒⋆ 1) (v 5) (v 8)

-- The intended m_f : p_f ; (m_x ◁ f)  ⇛  m_y ; q_f   (researcher eq. (1)).
mfTy : Ty
mfTy = arr (3 ⇒⋆ 1) (v 5) (c₁ 3 0 7 1 2)

mfSrc mfTgt : Tm
mfSrc = vcomp (v 3) (v 1) (v 5) (c₁ 3 0 4 1 2) (v 6) (c₁ 3 0 7 1 2)
              (whR (v 3) (v 0) (v 4) (v 7) (v 10) (v 1) (v 2))
mfTgt = vcomp (v 3) (v 1) (v 5) (v 8) (v 11) (c₁ 3 0 7 1 2) (v 9)

Marr : NCtx
Marr = Mpre ▹ 12 ∶ arr mfTy mfSrc mfTgt

------------------------------------------------------------------------
-- Sanity: the intended context is a well-formed CaTT context, and the
-- repaired rule accepts it.

intended-wf : WfCtx (ctrfCtx Γarr 3 Parr Qarr Marr)
intended-wf = from-just (wf? _)

open Ctrf
open CtrfCheck

intended-fixed : Ctrf1 fixed Γarr 3 Parr Qarr Marr
intended-fixed = from-just (ctrf? fixed Γarr 3 Parr Qarr Marr)

------------------------------------------------------------------------
-- D1: no m_f whose boundary type mentions q_x, for the printed rule
-- (any q_f) and for the rule with only the copy repaired.

private
  pfTy : Ty
  pfTy = arr (3 ⇒⋆ 1) (v 5) (c₁ 3 0 4 1 2)

  -- The context in which m_f's boundary is formed, and the set that the
  -- source condition τCond(s : A, p_f : X, FV(M₃)) requires FV(s : A)
  -- to equal (with the printed selector, testing τ of m_x, m_y).
  Kq : Ty → NCtx
  Kq Y = ctrfCtx Γarr 3 Parr (Qpre ▹ 9 ∶ Y) Mpre

  Rq : Ty → List Name
  Rq Y = fvVar (Kq Y) 6 ++ selector (Kq Y) τ (fvBdry τ pfTy) (names Mpre)

  -- q_x (7) is not in that set, whatever Y is.
  _ : ∀ {Y} → T (elem 7 (Rq Y)) → ⊥
  _ = λ ()

D1-printed : ∀ {Y A s t} → T (elem 7 (fvTy A)) →
             Ctrf1 printed Γarr 3 Parr (Qpre ▹ 9 ∶ Y) (Mpre ▹ 12 ∶ arr A s t) → ⊥
D1-printed {Y} {A} {s} h (close (dup _ _ _ _ h₁ _) _) =
  blocked 7 (fvTmTy s A) (Rq Y) (elem-++ʳ 7 (fvTm s) (fvTy A) h) (λ ())
    (∧-snd {linear (Kq Y) 6 s} h₁)
D1-printed h (close (newv (close _ ()) _ _) _)

D1-copyFixed : ∀ {Y A s t} → T (elem 7 (fvTy A)) →
               Ctrf1 copyFixed Γarr 3 Parr (Qpre ▹ 9 ∶ Y) (Mpre ▹ 12 ∶ arr A s t) → ⊥
D1-copyFixed {Y} {A} {s} h (close (dup _ _ _ _ h₁ _) _) =
  blocked 7 (fvTmTy s A) (Rq Y) (elem-++ʳ 7 (fvTm s) (fvTy A) h) (λ ())
    (∧-snd {linear (Kq Y) 6 s} h₁)
D1-copyFixed h (close (newv (close _ ()) _ _) _)

-- In particular the intended context is rejected by both.
D1-intended-printed : Ctrf1 printed Γarr 3 Parr Qarr Marr → ⊥
D1-intended-printed = D1-printed tt

D1-intended-copyFixed : Ctrf1 copyFixed Γarr 3 Parr Qarr Marr → ⊥
D1-intended-copyFixed = D1-copyFixed tt

------------------------------------------------------------------------
-- D2: with the printed copy, the duplicated block is never the cone Q,
-- whatever the comparison block is.

D2 : ∀ {M3} → Ctrf1 printed Γarr 3 Parr Qarr M3 → ⊥
D2 (close (dup _ _ () _ _ _) _)
D2 (close (newv (close (dup _ _ () _ _ _) _) _ _) _)
D2 (close (newv (close (newv (close (dup _ _ () _ _ _) _) _ _) _) _ _) _)
D2 (close (newv (close (newv (close (newv (close () _) _ _) _) _ _) _) _ _) _)

------------------------------------------------------------------------
-- D3: the gray rule (natural transformations, n = 1) over the arrow.
--   x0 y1 f2 | x′3 y′4 f′5 | p_x6 p_y7 p_f8

open Gray
open GrayCheck

G₁ G₂pre G₃pre : NCtx
G₁    = Γarr
G₂pre = ∅ ▹ 3 ∶ ⋆ ▹ 4 ∶ ⋆
G₃pre = ∅ ▹ 6 ∶ (0 ⇒⋆ 3) ▹ 7 ∶ (1 ⇒⋆ 4)

-- Mikhail's Example 4.1: p_f : f · p_y ⇒ p_x · f′.
ex41 : NCtx
ex41 = G₃pre ▹ 8 ∶ arr (0 ⇒⋆ 4) (c₁ 0 1 2 4 7) (c₁ 0 3 6 4 5)

G₂ : NCtx
G₂ = G₂pre ▹ 5 ∶ (3 ⇒⋆ 4)

ex41-fixed : Gray1 fixed G₁ G₂ ex41
ex41-fixed = from-just (gray? fixed G₁ G₂ ex41)

private
  Kg : Ty → NCtx
  Kg Y = grayCtx G₁ (G₂pre ▹ 5 ∶ Y) G₃pre

  Rg : Ty → List Name
  Rg Y = fvVar (Kg Y) 2 ++ selector (Kg Y) τ (fvBdry τ (0 ⇒⋆ 1)) (names G₃pre)

D3-printed : ∀ {Y A s t} → T (elem 4 (fvTy A)) →
             Gray1 printed G₁ (G₂pre ▹ 5 ∶ Y) (G₃pre ▹ 8 ∶ arr A s t) → ⊥
D3-printed {Y} {A} {s} h (close (dup _ _ _ _ h₁ _) _) =
  blocked 4 (fvTmTy s A) (Rg Y) (elem-++ʳ 4 (fvTm s) (fvTy A) h) (λ ())
    (∧-snd {linear (Kg Y) 2 s} h₁)
D3-printed h (close (newv (close _ ()) _) _)

D3-copyFixed : ∀ {Y A s t} → T (elem 4 (fvTy A)) →
               Gray1 copyFixed G₁ (G₂pre ▹ 5 ∶ Y) (G₃pre ▹ 8 ∶ arr A s t) → ⊥
D3-copyFixed {Y} {A} {s} h (close (dup _ _ _ _ h₁ _) _) =
  blocked 4 (fvTmTy s A) (Rg Y) (elem-++ʳ 4 (fvTm s) (fvTy A) h) (λ ())
    (∧-snd {linear (Kg Y) 2 s} h₁)
D3-copyFixed h (close (newv (close _ ()) _) _)

D3-ex41 : Gray1 printed G₁ G₂ ex41 → ⊥
D3-ex41 = D3-printed tt

------------------------------------------------------------------------
-- D4: what the printed rules accept over the arrow.

-- p_f : f ⇒ f′ with f′ : x → y (a parallel copy, not a second diagram).
degenerate-gray : Gray1 printed G₁ (G₂pre ▹ 5 ∶ (0 ⇒⋆ 1))
                    (G₃pre ▹ 8 ∶ arr (0 ⇒⋆ 1) (v 2) (v 5))
degenerate-gray = from-just (gray? printed _ _ _)

-- m_f : p_f ⇛ q_f with q_f : p_y ⇒ p_x f a parallel copy of p_f.
degenerate-ctrf : Ctrf1 printed Γarr 3 Parr
                    (Qpre ▹ 9 ∶ arr (3 ⇒⋆ 1) (v 5) (c₁ 3 0 4 1 2))
                    (Mpre ▹ 12 ∶ arr (arr (3 ⇒⋆ 1) (v 5) (c₁ 3 0 4 1 2)) (v 6) (v 9))
degenerate-ctrf = from-just (ctrf? printed _ _ _ _ _)

------------------------------------------------------------------------
-- D5: a non-canonical cone over the loop with a 2-cell.
--   x0 f1 α2 | c3 | q4 r5 b6

Γloop : NCtx
Γloop = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0) ▹ 2 ∶ arr (0 ⇒⋆ 0) (v 1) (v 1)

private
  qf qff : Tm
  qf  = c₁ 3 0 4 0 1                                   -- q · f
  qff = comp (v 3) (v 0) qf (v 0) (v 1)                 -- (q · f) · f

  -- r ◁ f : q f ⇒ (q f) f
  r◁f : Tm
  r◁f = whR (v 3) (v 0) (v 4) qf (v 5) (v 0) (v 1)

  -- s = r ; (r ◁ f) : q ⇒ (q f) f
  sNC : Tm
  sNC = vcomp (v 3) (v 0) (v 4) qf (v 5) qff r◁f

  -- t = s ; ((q f) ▷ α) : q ⇒ (q f) f
  tNC : Tm
  tNC = vcomp (v 3) (v 0) (v 4) qff sNC qff
              (whL (v 3) (v 0) qf (v 0) (v 1) (v 1) (v 2))

Πpre : NCtx
Πpre = ∅ ▹ 4 ∶ (3 ⇒⋆ 0) ▹ 5 ∶ arr (3 ⇒⋆ 0) (v 4) qf

-- The admitted non-canonical projection b : r ; (r ◁ f) ⇛ (r ; (r ◁ f)) ; (qf ▷ α).
Πnoncanonical : NCtx
Πnoncanonical = Πpre ▹ 6 ∶ arr (arr (3 ⇒⋆ 0) (v 4) qff) sNC tNC

-- The canonical projection (Thm 3.3): p_α : r ⇛ r ; (q ▷ α).
Πcanonical : NCtx
Πcanonical = Πpre ▹ 6 ∶ arr (arr (3 ⇒⋆ 0) (v 4) qf) (v 5)
                           (vcomp (v 3) (v 0) (v 4) qf (v 5) qf
                                  (whL (v 3) (v 0) (v 4) (v 0) (v 1) (v 1) (v 2)))

D5-noncanonical : Cone Γloop 3 Πnoncanonical
D5-noncanonical = from-just (cone? Γloop 3 Πnoncanonical)

D5-canonical : Cone Γloop 3 Πcanonical
D5-canonical = from-just (cone? Γloop 3 Πcanonical)

D5-distinct : Πnoncanonical ≡ Πcanonical → ⊥
D5-distinct ()
