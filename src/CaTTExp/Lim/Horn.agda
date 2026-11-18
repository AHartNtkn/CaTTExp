------------------------------------------------------------------------
-- B15, first slice: the horn form of the limit filler rule
-- (limits-metatheory.md §5.3), shared by P and L, over the arrow x → y,
-- for n = 0 and n = 1, on the specified shapes of CaTTExp.Cones.
--
-- Everything lives over the universal cone Pre = (x, y, f, L, λ_x,
-- λ_y, λ_f) (Cones.cone of the arrow, apex read as L). For a k-cell w
-- of 𝒦(c, L), F(w) is its image transfor under the universal cone:
--   F(u)_x = u ∗₀ λ_x,  F(u)_f = (u ∗₀ λ_f) ∗₁ assoc         (u : c → L)
--   F(U)_x = U ∗₀ λ_x,  F(U)_f = a pasting of associativity cohs and
--                                 the *forward* interchanger of U, λ_f
--                                                           (U : u⁻ ⇒ u⁺)
-- `inst` instantiates a shape (Cone or Tr_k) by sending its boundary
-- variables to given terms and keeping the others as new variables;
-- this is the substitution of §5.3 ("the boundary variables are
-- substituted by F(∂w)").
--
--  H1  Horn₀, Horn₁ and the rule's conclusions (J1: the n-cell uni^w;
--      J2: the components of the comparison E : T ⇛ F(uni^w), the new
--      variables of Tr_{n+1}) are well-formed contexts in the CaTT core
--      (P) and in the L core.
--  H2  (Not restated here.) For every σ : Θ → Horn_n the conclusions
--      are then well typed in Θ, by admissibility of substitution in
--      each core (CaTTExp.Subst; Gray.Pure.substL).
--  H3  The switch: Horn₁'s comparison variable over f (m_f) is a marked
--      declaration under P, and under L iff f is marked; Horn₀ has
--      none. (The J2 outputs are certified in both.)
--  H4  Under L, F(U)_f uses the forward interchanger only. Its
--      canonical inverse pasting (each step reversed) is a term of
--      CaTT but not of L. The reverse interchanger at (U, λ_f) is not a
--      term of L, while the other coherences it pastes are. This rules out that pasting, not every
--      inverse term (that is Thm 1(2), open).
------------------------------------------------------------------------
module CaTTExp.Lim.Horn where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
import CaTTExp.Gray.Pure as L
open import CaTTExp.Cones

------------------------------------------------------------------------
-- Instantiation of a shape.

-- Walk the shape S; a variable with an assigned term is sent to it,
-- any other becomes a new variable of the result (typed by the image
-- of its type). Returns the extended context and the substitution
-- S → result.
inst : Ctx → Ctx → (Nat → Maybe Tm) → Ctx × List Tm
inst P S b = go (toList S) P []
  where
  toList : Ctx → List Ty
  toList ε       = []
  toList (Γ ▸ A) = toList Γ ++ (A ∷ [])
  go : List Ty → Ctx → List Tm → Ctx × List Tm
  go []       H ι = H , ι
  go (A ∷ As) H ι with b (length ι)
  ... | just t  = go As H (ι ++ (t ∷ []))
  ... | nothing = go As (H ▸ A [ ⟪ ι ⟫ ]ty) (ι ++ (var (len H) ∷ []))

------------------------------------------------------------------------
-- Coherences over a pasting context.

cohOn : Ctx → Cell → Cell → List Tm → Cell
cohOn P s t ts = coh P A ⟪ ts ⟫ , A [ ⟪ ts ⟫ ]ty
  where A = arr (snd s) (fst s) (fst t)

private
  -- boundary 0-cells of a 1-cell / of the 1-cells under a 2-cell
  s0 t0 : Cell → Tm
  s0 u = fst (srcC u)
  t0 u = fst (tgtC u)
  s1 t1 : Cell → Cell
  s1 = srcC
  t1 = tgtC

Comp₃ HCompP VComp₃² NatP : Ctx
Comp₃    = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))
HCompP   = ctxOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []))
VComp₃²  = ctxOf (node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ []))
NatP     = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ leaf ∷ []))

-- assoc(p, q, r) : p ∗₀ (q ∗₀ r) ⇒ (p ∗₀ q) ∗₀ r   (1-cells)
assoc : Cell → Cell → Cell → Cell
assoc p q r = cohOn Comp₃ (binC 0 P (binC 0 Q R)) (binC 0 (binC 0 P Q) R)
                (s0 p ∷ t0 p ∷ fst p ∷ t0 q ∷ fst q ∷ t0 r ∷ fst r ∷ [])
  where g = gen Comp₃ ; P = g 2 ; Q = g 4 ; R = g 6

-- nat(U, h, k) : assoc(u⁻,h,k) ∗₁ ((U ∗₀ h) ∗₀ k) ⇛ (U ∗₀ (h ∗₀ k)) ∗₁ assoc(u⁺,h,k)
nat : Cell → Cell → Cell → Cell
nat U h k = cohOn NatP
  (binC 1 (assoc u⁻ Hh Kk) (binC 0 (binC 0 V Hh) Kk))
  (binC 1 (binC 0 V (binC 0 Hh Kk)) (assoc u⁺ Hh Kk))
  (s0 (s1 U) ∷ t0 (s1 U) ∷ fst (s1 U) ∷ fst (t1 U) ∷ fst U
   ∷ t0 h ∷ fst h ∷ t0 k ∷ fst k ∷ [])
  where g = gen NatP ; u⁻ = g 2 ; u⁺ = g 3 ; V = g 4 ; Hh = g 6 ; Kk = g 8

natR : Cell → Cell → Cell → Cell
natR U h k = cohOn NatP
  (binC 1 (binC 0 V (binC 0 Hh Kk)) (assoc u⁺ Hh Kk))
  (binC 1 (assoc u⁻ Hh Kk) (binC 0 (binC 0 V Hh) Kk))
  (s0 (s1 U) ∷ t0 (s1 U) ∷ fst (s1 U) ∷ fst (t1 U) ∷ fst U
   ∷ t0 h ∷ fst h ∷ t0 k ∷ fst k ∷ [])
  where g = gen NatP ; u⁻ = g 2 ; u⁺ = g 3 ; V = g 4 ; Hh = g 6 ; Kk = g 8

-- vertical associativity of 2-cells, both directions
avL avR : Cell → Cell → Cell → Cell
avL p q r = cohOn VComp₃² (binC 1 (binC 1 P Q) R) (binC 1 P (binC 1 Q R)) (vargs p q r)
  where g = gen VComp₃² ; P = g 4 ; Q = g 6 ; R = g 8
        vargs : Cell → Cell → Cell → List Tm
        vargs p q r = s0 (s1 p) ∷ t0 (s1 p) ∷ fst (s1 p) ∷ fst (t1 p) ∷ fst p
                      ∷ fst (t1 q) ∷ fst q ∷ fst (t1 r) ∷ fst r ∷ []
avR p q r = cohOn VComp₃² (binC 1 P (binC 1 Q R)) (binC 1 (binC 1 P Q) R)
                (s0 (s1 p) ∷ t0 (s1 p) ∷ fst (s1 p) ∷ fst (t1 p) ∷ fst p
                 ∷ fst (t1 q) ∷ fst q ∷ fst (t1 r) ∷ fst r ∷ [])
  where g = gen VComp₃² ; P = g 4 ; Q = g 6 ; R = g 8

-- The forward interchanger (Gray.Examples.ich, in binC form):
--   (f ◁ β) ∗₁ (α ▷ g')  ⇛  (α ▷ g) ∗₁ (f' ◁ β)
ichF : Cell → Cell → Cell
ichF α β = cohOn HCompP
  (binC 1 (binC 0 f β') (binC 0 α' g'))
  (binC 1 (binC 0 α' g) (binC 0 f' β'))
  (s0 (s1 α) ∷ t0 (s1 α) ∷ fst (s1 α) ∷ fst (t1 α) ∷ fst α
   ∷ t0 (s1 β) ∷ fst (s1 β) ∷ fst (t1 β) ∷ fst β ∷ [])
  where h = gen HCompP ; f = h 2 ; f' = h 3 ; α' = h 4 ; g = h 6 ; g' = h 7 ; β' = h 8

-- The reverse interchanger, as a CaTT coh (L has no such coh).
ichR : Cell → Cell → Cell
ichR α β = cohOn HCompP
  (binC 1 (binC 0 α' g) (binC 0 f' β'))
  (binC 1 (binC 0 f β') (binC 0 α' g'))
  (s0 (s1 α) ∷ t0 (s1 α) ∷ fst (s1 α) ∷ fst (t1 α) ∷ fst α
   ∷ t0 (s1 β) ∷ fst (s1 β) ∷ fst (t1 β) ∷ fst β ∷ [])
  where h = gen HCompP ; f = h 2 ; f' = h 3 ; α' = h 4 ; g = h 6 ; g' = h 7 ; β' = h 8

------------------------------------------------------------------------
-- The universal cone over the arrow and the image transfors F(w).

Arr : ExCtx
Arr = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ []

ConeCtx Tr₁ Tr₂ : Ctx
ConeCtx = evCtx (ConeOf.cone Arr)                 -- x0 y1 f2 c3 p_x4 p_y5 p_f6
Tr₁     = evCtx (Ctrf.ctx (from-just (ctrf 1 Arr)))
Tr₂     = evCtx (Ctrf.ctx (from-just (ctrf 2 Arr)))

-- Pre: x0 y1 f2 L3 λ_x4 λ_y5 λ_f6
Pre : Ctx
Pre = ConeCtx

module U (Θ : Ctx) where
  -- the universal cone, read in any extension Θ of Pre
  f λx λy λf : Cell
  f  = gen Θ 2 ; λx = gen Θ 4 ; λy = gen Θ 5 ; λf = gen Θ 6

  F₀x F₀y F₀f : Cell → Cell                       -- u : c → L
  F₀x u = binC 0 u λx
  F₀y u = binC 0 u λy
  F₀f u = binC 1 (binC 0 u λf) (assoc u λx f)

  -- F(U)_f, given the interchanger cell to use
  F₁fWith : (Cell → Cell → Cell) → Cell → Cell

  F₁x F₁y F₁f : Cell → Cell                       -- U : u⁻ ⇒ u⁺
  F₁x U = binC 0 U λx
  F₁y U = binC 0 U λy
  F₁f = F₁fWith ichF

  F₁fWith ich U = binC 2 (binC 2 (binC 2 (binC 2 st1 st2) st3) st4) st5
    where
    u⁻ = s1 U ; u⁺ = t1 U
    P  = binC 0 u⁻ λf ; P⁺ = binC 0 u⁺ λf
    a⁻ = assoc u⁻ λx f ; a⁺ = assoc u⁺ λx f
    Z  = binC 0 (binC 0 U λx) f
    W  = binC 0 U (binC 0 λx f)
    Uy = binC 0 U λy
    st1 = avL P a⁻ Z
    st2 = binC 1 P (nat U λx f)
    st3 = avR P W a⁺
    st4 = binC 1 (ich U λf) a⁺
    st5 = avL Uy P⁺ a⁺

  -- The canonical inverse pasting RHS ⇛ LHS of F(U)_f: every step
  -- reversed. Its interchanger step is the reverse coh.
  F₁fInv : Cell → Cell
  F₁fInv U = binC 2 (binC 2 (binC 2 (binC 2 r1 r2) r3) r4) r5
    where
    u⁻ = s1 U ; u⁺ = t1 U
    P  = binC 0 u⁻ λf ; P⁺ = binC 0 u⁺ λf
    a⁻ = assoc u⁻ λx f ; a⁺ = assoc u⁺ λx f
    Z  = binC 0 (binC 0 U λx) f
    W  = binC 0 U (binC 0 λx f)
    Uy = binC 0 U λy
    r1 = avR Uy P⁺ a⁺
    r2 = binC 1 (ichR U λf) a⁺
    r3 = avL P W a⁺
    r4 = binC 1 P (natR U λx f)
    r5 = avR P a⁻ Z

------------------------------------------------------------------------
-- n = 0.  Horn₀ = Cone(Γ; c)[γ]: Pre, c7, p_x8, p_y9, p_f10.

Horn₀ : Ctx
Horn₀ = fst (inst Pre ConeCtx (λ i → if i <ℕ 3 then just (var i) else nothing))

-- J1: U11 : c → L.
J1₀ : Ctx
J1₀ = Horn₀ ▸ arr ⋆ (var 7) (var 3)

-- J2: E : T ⇛ F(U), the new variables m_x, m_y, m_f of Tr₁.
-- Tr₁: x0 y1 f2 c3 p⁻_x4 p⁺_x5 m_x6 p⁻_y7 p⁺_y8 m_y9 p⁻_f10 p⁺_f11 m_f12.
J2₀ : Ctx
J2₀ = fst (inst J1₀ Tr₁ (nth nothing tbl))
  where
  open U J1₀
  Uc = gen J1₀ 11
  tbl : List (Maybe Tm)
  tbl = just (var 0) ∷ just (var 1) ∷ just (var 2) ∷ just (var 7)
      ∷ just (var 8)  ∷ just (fst (F₀x Uc)) ∷ nothing
      ∷ just (var 9)  ∷ just (fst (F₀y Uc)) ∷ nothing
      ∷ just (var 10) ∷ just (fst (F₀f Uc)) ∷ nothing ∷ []

------------------------------------------------------------------------
-- n = 1.  Boundary sphere u⁻8 u⁺9 : c7 → L; Horn₁ = Pre, c, u⁻, u⁺,
-- m_x10, m_y11, m_f12 with p^± ↦ F(u^±).

H₁pre : Ctx
H₁pre = Pre ▸ ⋆ ▸ arr ⋆ (var 7) (var 3) ▸ arr ⋆ (var 7) (var 3)

Horn₁inst : Ctx × List Tm
Horn₁inst = inst H₁pre Tr₁ (nth nothing tbl)
  where
  open U H₁pre
  u⁻ = gen H₁pre 8 ; u⁺ = gen H₁pre 9
  tbl : List (Maybe Tm)
  tbl = just (var 0) ∷ just (var 1) ∷ just (var 2) ∷ just (var 7)
      ∷ just (fst (F₀x u⁻)) ∷ just (fst (F₀x u⁺)) ∷ nothing
      ∷ just (fst (F₀y u⁻)) ∷ just (fst (F₀y u⁺)) ∷ nothing
      ∷ just (fst (F₀f u⁻)) ∷ just (fst (F₀f u⁺)) ∷ nothing ∷ []

Horn₁ : Ctx
Horn₁ = fst Horn₁inst

-- J1: U13 : u⁻ ⇒ u⁺.
J1₁ : Ctx
J1₁ = Horn₁ ▸ arr (arr ⋆ (var 7) (var 3)) (var 8) (var 9)

-- J2: the new variables μ_x, μ_y, μ_f of Tr₂.
-- Tr₂: x0 y1 f2 c3 | p⁻_x4 p⁺_x5 m⁻_x6 m⁺_x7 μ_x8 | p⁻_y9 p⁺_y10 m⁻_y11
--      m⁺_y12 μ_y13 | p⁻_f14 p⁺_f15 m⁻_f16 m⁺_f17 μ_f18.
J2₁ : Ctx
J2₁ = fst (inst J1₁ Tr₂ (nth nothing tbl))
  where
  open U J1₁
  u⁻ = gen J1₁ 8 ; u⁺ = gen J1₁ 9 ; Uc = gen J1₁ 13
  tbl : List (Maybe Tm)
  tbl = just (var 0) ∷ just (var 1) ∷ just (var 2) ∷ just (var 7)
      ∷ just (fst (F₀x u⁻)) ∷ just (fst (F₀x u⁺)) ∷ just (var 10) ∷ just (fst (F₁x Uc)) ∷ nothing
      ∷ just (fst (F₀y u⁻)) ∷ just (fst (F₀y u⁺)) ∷ just (var 11) ∷ just (fst (F₁y Uc)) ∷ nothing
      ∷ just (fst (F₀f u⁻)) ∷ just (fst (F₀f u⁺)) ∷ just (var 12) ∷ just (fst (F₁f Uc)) ∷ nothing ∷ []

------------------------------------------------------------------------
-- H1. Well formed in both cores.

okP okL : Ctx → Bool
okP Γ = is-just (checkCtx Γ)
okL Γ = is-just (L.checkCtx Γ)

_ : (okP Horn₀ ∧ okP J1₀ ∧ okP J2₀) ≡ true
_ = refl
_ : (okP Horn₁ ∧ okP J1₁ ∧ okP J2₁) ≡ true
_ = refl
_ : (okL Horn₀ ∧ okL J1₀ ∧ okL J2₀) ≡ true
_ = refl
_ : (okL Horn₁ ∧ okL J1₁ ∧ okL J2₁) ≡ true
_ = refl

------------------------------------------------------------------------
-- H3. The P/L switch on Horn₁. Tr₁ marks its comparison over f (level
-- 12), and inst sends it to the new variable 12 of Horn₁.

_ : Ctrf.marked (from-just (ctrf 1 Arr)) ≡ (12 ∷ [])
_ = refl
_ : nth (var 0) (snd Horn₁inst) 12 ≡ var 12
_ = refl

-- Marked declarations of Horn₁: under P, every comparison over a
-- positive-dimensional generator; under L, those over the marked
-- generators μ (f is level 2). Horn₀ has no comparison variables.
marksP₁ : List Nat
marksP₁ = 12 ∷ []

marksL₁ : List Nat → List Nat
marksL₁ μ = if elem 2 μ then marksP₁ else []

_ : (marksL₁ [] ∷ marksL₁ (2 ∷ []) ∷ []) ≡ ([] ∷ marksP₁ ∷ [])
_ = refl

-- Sizes: the boundary variables were substituted, the others kept.
_ : (len Horn₀ ∷ len J2₀ ∷ len Horn₁ ∷ len J2₁ ∷ []) ≡ (11 ∷ 15 ∷ 13 ∷ 17 ∷ [])
_ = refl

------------------------------------------------------------------------
-- H4. The direction matters. In the J2₁ context, the comparison over f
-- of F(U) with its two endpoints swapped (U : u⁺ ⇒ u⁻ … ) is not
-- needed; what the collapse needs is an *inverse* of F(U)_f. Its
-- interchanger step would be the reverse coh: CaTT has it, L does not.

tmP tmL : Ctx → Cell → Bool
tmP Γ c = is-just (infer Γ (fst c))
tmL Γ c = is-just (L.infer Γ (fst c))

ichRAt ichFAt : Cell
ichRAt = ichR (gen J1₁ 13) (gen J1₁ 6)      -- at (U, λ_f)
ichFAt = ichF (gen J1₁ 13) (gen J1₁ 6)

_ : (tmP J1₁ ichRAt ∧ tmP J1₁ ichFAt ∧ tmL J1₁ ichFAt) ≡ true
_ = refl
_ : tmL J1₁ ichRAt ≡ false
_ = refl

-- Hence F(U)_f is formed in L (it also occurs in J2₁'s types, H1),
-- while its canonical inverse pasting is a term of CaTT but not of L;
-- the other coherences that pasting uses are terms of L.
module _ where
  open U J1₁
  Uc = gen J1₁ 13
  u⁻ = s1 Uc ; u⁺ = t1 Uc

  _ : tmP J1₁ (F₁fInv Uc) ≡ true
  _ = refl
  _ : tmL J1₁ (F₁fInv Uc) ≡ false
  _ = refl
  _ : (tmL J1₁ (natR Uc λx f) ∧ tmL J1₁ (avR (binC 0 Uc λy) (binC 0 u⁺ λf) (assoc u⁺ λx f))
       ∧ tmL J1₁ (avL (binC 0 u⁻ λf) (binC 0 Uc (binC 0 λx f)) (assoc u⁺ λx f))
       ∧ tmL J1₁ (avR (binC 0 u⁻ λf) (assoc u⁻ λx f) (binC 0 (binC 0 Uc λx) f))) ≡ true
  _ = refl
_ : (tmP J1₁ (U.F₁f J1₁ (gen J1₁ 13)) ∧ tmL J1₁ (U.F₁f J1₁ (gen J1₁ 13))) ≡ true
_ = refl
