------------------------------------------------------------------------
-- Horns Horn_n(Γ) for every globular diagram Γ of dimension ≤ 1 and
-- n = 0, 1 (ledger S27 (e′); spec §6.2), generalising CaTTExp.Lim.Horn
-- from the arrow.
--
-- Over a diagram Γ of dimension ≤ 1 the transfor contexts Tr_k of
-- CaTTExp.Cones have a uniform layout: Γ, the apex c, then for every
-- variable x of Γ a block of 2k + 1 variables (the boundary pairs, then
-- the top). A horn is Tr_n instantiated (`Horn.inst`) with the boundary
-- pairs sent to F(∂w), and the J2 context is Tr_{n+1} instantiated with
-- its boundary pairs sent to F(∂w), (the horn's top, F(w)). F is the
-- image under the universal cone, given generator by generator:
--
--   F(u)_x = u ∗₀ λ_x,  F(u)_f = (u ∗₀ λ_f) ∗₁ assoc(u, λ_a, f)     (u : c → L)
--   F(U)_x = U ∗₀ λ_x,  F(U)_f = the five-step pasting of Lim/Horn     (U : u⁻ ⇒ u⁺)
--
-- for x an object and f : a → b an arrow of Γ (Lim/Horn's formulas, with
-- the arrow's levels replaced by f's). The result is laid out as
-- CaTTExp.Binder.UniHeads expects: Cone(Γ; L), c, the sphere ∂w, the
-- horn tops, w, the components; `hornShape` packs it with the marked
-- horn entries (the comparisons over arrows, CaTT's setting).
--
-- Nothing here is assumed well formed: the uni heads decide it (their
-- validity runs the certified checker on the whole context), and
-- CaTTExp.Binder.HornGenExamples checks it on a suite of diagrams.
------------------------------------------------------------------------
module CaTTExp.Lim.HornGen where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Cones
open import CaTTExp.Lim.Horn using (inst; cohOn; assoc; nat; avL; avR; ichF)

------------------------------------------------------------------------
-- Diagrams as expression contexts.

toExTy : Ty → Maybe ExTy
toExTy ⋆ = just ob
toExTy (arr A (var i) (var j)) = toExTy A >>= λ E → just (hom E (v i) (v j))
toExTy _ = nothing

toExCtx : Ctx → Maybe ExCtx
toExCtx ε       = just []
toExCtx (Γ ▸ A) = toExCtx Γ >>= λ E → toExTy A >>= λ X → just (E ++ (X ∷ []))

-- Dimension at most d.
dimLe : Nat → Ctx → Bool
dimLe d ε       = true
dimLe d (Γ ▸ A) = dimLe d Γ ∧ (dim A <ℕ suc d)

------------------------------------------------------------------------
-- Two coherences over pasting contexts, for 2-dimensional generators.

private
  s0 t0 : Cell → Tm
  s0 u = fst (srcC u)
  t0 u = fst (tgtC u)

-- U ∗₀ (X ∗₁ Z) ⇒ (U ∗₀ X) ∗₁ (U ∗₀ Z)   (U a 1-cell, X, Z 2-cells)
-- over c0 L1 U2 z3 m₀4 m₁5 X6 m₂7 Z8.
DistP : Ctx
DistP = ctxOf (node (leaf ∷ node (leaf ∷ leaf ∷ []) ∷ []))

dist : Cell → Cell → Cell → Cell
dist U X Z = cohOn DistP (binC 0 Ug (binC 1 Xg Zg)) (binC 1 (binC 0 Ug Xg) (binC 0 Ug Zg))
  (s0 U ∷ t0 U ∷ fst U ∷ t0 (srcC X) ∷ fst (srcC X) ∷ fst (tgtC X) ∷ fst X
   ∷ fst (tgtC Z) ∷ fst Z ∷ [])
  where g = gen DistP ; Ug = g 2 ; Xg = g 6 ; Zg = g 8

-- Naturality of assoc in its third argument (α : f ⇒ g):
--   (U ∗₀ (h ∗₀ α)) ∗₁ assoc(U, h, g) ⇛ assoc(U, h, f) ∗₁ ((U ∗₀ h) ∗₀ α)
-- over c0 L1 U2 a3 h4 b5 f6 g7 α8.
NatαP : Ctx
NatαP = ctxOf (node (leaf ∷ leaf ∷ node (leaf ∷ []) ∷ []))

natα : Cell → Cell → Cell → Cell
natα U h α = cohOn NatαP
  (binC 1 (binC 0 Ug (binC 0 Hg Ag)) (assoc Ug Hg Gg))
  (binC 1 (assoc Ug Hg Fg) (binC 0 (binC 0 Ug Hg) Ag))
  (s0 U ∷ t0 U ∷ fst U ∷ t0 h ∷ fst h ∷ t0 (srcC α) ∷ fst (srcC α) ∷ fst (tgtC α) ∷ fst α ∷ [])
  where g = gen NatαP ; Ug = g 2 ; Hg = g 4 ; Fg = g 6 ; Gg = g 7 ; Ag = g 8

------------------------------------------------------------------------
-- The image of a cell under the universal cone, in any context Θ
-- extending the cone context Pre of Γ.

module Img (Γ : Ctx) (Θ : Ctx) where
  nΓ = len Γ

  λg : Nat → Cell
  λg x = gen Θ (suc (nΓ + x))

  -- The endpoints of an arrow of Γ (0, 0 for an object).
  ends : Nat → Nat × Nat
  ends x with lookup Γ x
  ... | just (arr ⋆ (var a) (var b)) = a , b
  ... | _                             = 0 , 0

  isArr : Nat → Bool
  isArr x with lookup Γ x
  ... | just (arr ⋆ _ _) = true
  ... | _                = false

  -- For a 2-cell α : f ⇒ g of Γ: (a, f, g).
  ends₂ : Nat → Nat × (Nat × Nat)
  ends₂ x with lookup Γ x
  ... | just (arr (arr ⋆ (var a) (var b)) (var f) (var g)) = a , (f , g)
  ... | _                                                   = 0 , (0 , 0)

  isTwo : Nat → Bool
  isTwo x with lookup Γ x
  ... | just (arr (arr ⋆ _ _) _ _) = true
  ... | _                          = false

  -- u : c → L.
  F₀ : Nat → Cell → Cell
  F₀ x u =
    if isArr x
    then binC 1 (binC 0 u (λg x)) (assoc u (λg (fst (ends x))) (gen Θ x))
    else if isTwo x then F₀α
    else binC 0 u (λg x)
    where
    -- α : f ⇒ g over a → b; λ_α : λ_g ⇛ λ_f ∗₁ (λ_a ∗₀ α).
    a = fst (ends₂ x) ; f = fst (snd (ends₂ x)) ; g = snd (snd (ends₂ x))
    α = gen Θ x
    λa = λg a ; λf = λg f ; λα = λg x
    Ag = assoc u λa (gen Θ g) ; Af = assoc u λa (gen Θ f)
    P  = binC 0 u λf
    Q  = binC 0 u (binC 0 λa α)
    Z′ = binC 0 (binC 0 u λa) α
    s1 = binC 1 (binC 0 u λα) Ag
    s2 = binC 1 (dist u λf (binC 0 λa α)) Ag
    s3 = avL P Q Ag
    s4 = binC 1 P (natα u λa α)
    s5 = avR P Af Z′
    F₀α = binC 2 (binC 2 (binC 2 (binC 2 s1 s2) s3) s4) s5

  -- U : u⁻ ⇒ u⁺, as in Lim/Horn (forward interchanger).
  F₁ : Nat → Cell → Cell
  F₁ x U =
    if isArr x
    then binC 2 (binC 2 (binC 2 (binC 2 st1 st2) st3) st4) st5
    else binC 0 U (λg x)
    where
    a = fst (ends x)
    b = snd (ends x)
    f = gen Θ x
    λa = λg a ; λb = λg b ; λf = λg x
    u⁻ = srcC U ; u⁺ = tgtC U
    P  = binC 0 u⁻ λf ; P⁺ = binC 0 u⁺ λf
    a⁻ = assoc u⁻ λa f ; a⁺ = assoc u⁺ λa f
    Z  = binC 0 (binC 0 U λa) f
    W  = binC 0 U (binC 0 λa f)
    Ub = binC 0 U λb
    st1 = avL P a⁻ Z
    st2 = binC 1 P (nat U λa f)
    st3 = avR P W a⁺
    st4 = binC 1 (ichF U λf) a⁺
    st5 = avL Ub P⁺ a⁺

------------------------------------------------------------------------
-- The constructions.

record HornData : Set where
  constructor hd
  field
    J2     : Ctx
    horn   : Nat
    marked : List Nat

module Build (Γ : Ctx) (E : ExCtx) where
  nΓ  = len Γ
  Pre = evCtx (ConeOf.cone E)
  cL  = suc (nΓ + nΓ)          -- the level of c, right after Pre
  Lv  = nΓ                     -- the level of L in Pre

  -- Tables over the per-variable blocks of Tr_k: entry j of block x.
  blockTbl : Nat → (Nat → Nat → Maybe Tm) → List (Maybe Tm)
  blockTbl k f = concatMap (λ x → map (f x) (range (suc (k + k)))) (range nΓ)

  front : List (Maybe Tm)
  front = map (λ i → just (var i)) (range nΓ) ++ (just (var cL) ∷ [])

  trCtx : Nat → Maybe Ctx
  trCtx k = ctrf k E >>= λ T → just (evCtx (Ctrf.ctx T))

  trMarked : Nat → List Nat
  trMarked k = mk (ctrf k E)
    where
    mk : Maybe Ctrf → List Nat
    mk (just T) = Ctrf.marked T
    mk nothing  = []

  -- n = 0. Horn₀ = Cone(Γ; c)[γ] over Pre; w = U : c → L.
  horn₀ : Ctx × List Tm
  horn₀ = inst Pre Pre (λ i → if i <ℕ nΓ then just (var i) else nothing)

  J1₀ : Ctx
  J1₀ = fst horn₀ ▸ arr ⋆ (var cL) (var Lv)

  J2₀ : Maybe Ctx
  J2₀ = trCtx 1 >>= λ T₁ → just (fst (inst J1₀ T₁ (nth nothing tbl)))
    where
    open Img Γ J1₀
    Uc = gen J1₀ (len J1₀ ∸ 1)
    -- block x of Tr₁: p⁻_x ↦ the horn's p_x, p⁺_x ↦ F(U)_x, m_x new.
    tbl : List (Maybe Tm)
    tbl = front ++ blockTbl 1 (λ x j →
            if j ==ℕ 0 then just (var (suc (cL + x)))
            else if j ==ℕ 1 then just (fst (F₀ x Uc)) else nothing)

  -- n = 1. Sphere u⁻, u⁺ : c → L; Horn₁ = Tr₁ with p^± ↦ F(u^±).
  H₁pre : Ctx
  H₁pre = Pre ▸ ⋆ ▸ arr ⋆ (var cL) (var Lv) ▸ arr ⋆ (var cL) (var Lv)

  horn₁ : Maybe (Ctx × List Tm)
  horn₁ = trCtx 1 >>= λ T₁ → just (inst H₁pre T₁ (nth nothing tbl))
    where
    open Img Γ H₁pre
    u⁻ = gen H₁pre (suc cL) ; u⁺ = gen H₁pre (suc (suc cL))
    tbl : List (Maybe Tm)
    tbl = front ++ blockTbl 1 (λ x j →
            if j ==ℕ 0 then just (fst (F₀ x u⁻))
            else if j ==ℕ 1 then just (fst (F₀ x u⁺)) else nothing)

  J2₁ctx : Maybe Ctx
  J2₁ctx = horn₁ >>= λ H → trCtx 2 >>= λ T₂ → just (fst (inst (J1 H) T₂ (nth nothing (tbl H))))
    where
    J1 : Ctx × List Tm → Ctx
    J1 H = fst H ▸ arr (arr ⋆ (var cL) (var Lv)) (var (suc cL)) (var (suc (suc cL)))
    tbl : Ctx × List Tm → List (Maybe Tm)
    tbl H = front ++ blockTbl 2 (λ x j →
              if j ==ℕ 0 then just (fst (F₀ x u⁻))
              else if j ==ℕ 1 then just (fst (F₀ x u⁺))
              else if j ==ℕ 2 then just (var (cL + 3 + x))
              else if j ==ℕ 3 then just (fst (F₁ x Uc)) else nothing)
      where
      open Img Γ (J1 H)
      u⁻ = gen (J1 H) (suc cL) ; u⁺ = gen (J1 H) (suc (suc cL))
      Uc = gen (J1 H) (len (fst H))

  -- Horn₁'s marked entries: Tr₁'s marked levels, carried by inst.
  marks₁ : List Nat
  marks₁ = mk horn₁
    where
    isVar′ : Tm → List Nat
    isVar′ (var j) = j ∷ []
    isVar′ _       = []
    mk : Maybe (Ctx × List Tm) → List Nat
    mk nothing  = []
    mk (just H) = concatMap (λ l → isVar′ (nth (var 0) (snd H) l)) (trMarked 1)

-- The horn shape at (Γ, n), for Γ globular of dimension ≤ 1.
hornAt : Ctx → ExCtx → Nat → Maybe HornData
hornAt Γ E zero          = Build.J2₀ Γ E >>= λ J → just (hd J (suc (len Γ)) [])
hornAt Γ E (suc zero)    = Build.J2₁ctx Γ E >>= λ J → just (hd J (3 + len Γ) (Build.marks₁ Γ E))
hornAt Γ E (suc (suc _)) = nothing

-- The hand-built horns (Lim/Horn's formulas generalised; n = 0, 1).
hornDataHand : Ctx → Nat → Maybe HornData
hornDataHand Γ zero    = if dimLe 2 Γ then (toExCtx Γ >>= λ E → hornAt Γ E zero) else nothing
hornDataHand Γ (suc n) = if dimLe 1 Γ then (toExCtx Γ >>= λ E → hornAt Γ E (suc n)) else nothing

------------------------------------------------------------------------
-- Every n, for diagrams of dimension ≤ 1 (S27 (e′)).
--
-- F(w) is the n-fold cylinder lift of F(u) (CaTTExp.Cones, ledger
-- B18): put u : c → L after the cone context Pre, take F(u)_x as
-- above (as expressions), and lift n times along the newest variable.
-- Stage k is the context Pre, c, the k-sphere and w (Θ_k), with, for
-- each x of Γ, the images of the boundary pairs of block x of Tr_k and
-- F_k(w)_x. Lifting F_k along w gives F_{k+1}; its two copies become
-- the new boundary pair. Horn_n is Tr_n with the boundary pairs sent
-- to stage n's images; J2_n is Tr_{n+1} with, in addition, the pair
-- (horn top, F_n(w)).

module Gen (Γ : Ctx) (E : ExCtx) where
  nΓ = len Γ
  cL = suc (nΓ + nΓ)
  Lv = nΓ
  uL = suc cL

  Θ₀ : ExCtx
  Θ₀ = ConeOf.cone E ++ (ob ∷ hom ob (v cL) (v Lv) ∷ [])

  -- F(u)_x: u ∗₀ λ_x over an object, and over an arrow f : a → b
  -- (u ∗₀ λ_f) ∗₁ assoc(u, λ_a, f), where assoc is the reverse
  -- associator u ∗₀ (λ_a ∗₀ f) → (u ∗₀ λ_a) ∗₀ f.
  F0 : Nat → Ex
  F0 x = pick (nth ob E x)
    where
    λx = v (suc (nΓ + x))
    pick : ExTy → Ex
    pick (hom ob (v a) (v b)) =
      bn 1 (bn 0 (v uL) λx) (asCh 1 false (v uL) (v (suc (nΓ + a))) (v x))
    pick _ = bn 0 (v uL) λx

  Stage : Set
  Stage = ExCtx × List (List Ex × Ex)

  private
    seqS : List (Maybe (List Ex × Ex)) → Maybe (List (List Ex × Ex))
    seqS []       = just []
    seqS (m ∷ ms) = m >>= λ p → seqS ms >>= λ ps → just (p ∷ ps)

    step : Stage → Maybe Stage
    step (Θ , xs) =
      cyCtx (fuelOf Θ) Θ Y >>= λ Θ' →
      seqS (map one xs) >>= λ xs' →
      just (Θ' , xs')
      where
      Y = (length Θ ∸ 1) ∷ []
      one : List Ex × Ex → Maybe (List Ex × Ex)
      one (bs , F) = cyLift (fuelOf Θ) Θ Y F >>= λ F' →
        just (map (cyRenM Y) bs ++ (cyRenM Y F ∷ cyRenP Y F ∷ []) , F')

  stage : Nat → Maybe Stage
  stage zero    = just (Θ₀ , map (λ x → [] , F0 x) (range nΓ))
  stage (suc k) = stage k >>= step

  trCtx : Nat → Maybe Ctx
  trCtx k = ctrf k E >>= λ T → just (evCtx (Ctrf.ctx T))

  trMarked : Nat → List Nat
  trMarked k = mk (ctrf k E)
    where
    mk : Maybe Ctrf → List Nat
    mk (just T) = Ctrf.marked T
    mk nothing  = []

  front : List (Maybe Tm)
  front = map (λ i → just (var i)) (range nΓ) ++ (just (var cL) ∷ [])

  takeE : Nat → ExCtx → ExCtx
  takeE zero    _        = []
  takeE (suc n) []       = []
  takeE (suc n) (A ∷ As) = A ∷ takeE n As

  module At (n : Nat) (S : Stage) where
    Θ   = fst S
    xs  = snd S
    pre = length Θ ∸ 1                       -- the level of w in Θ
    Hpre : Ctx                               -- Pre, c, the sphere
    Hpre = evCtxGo Θ (takeE pre Θ) ε
    wTy : Ty
    wTy = evTy Θ (nth ob Θ pre)

    bnd : Nat → Nat → Maybe Tm               -- boundary pair j of block x
    bnd x j = just (ev Θ (nth (v 0) (fst (nth ([] , v 0) xs x)) j))

    hornTbl : List (Maybe Tm)
    hornTbl = front ++ concatMap (λ x → map (λ j → if j <ℕ (n + n) then bnd x j else nothing)
                                             (range (suc (n + n)))) (range nΓ)

    horn : Maybe (Ctx × List Tm)
    horn = trCtx n >>= λ T → just (inst Hpre T (nth nothing hornTbl))

    -- F_n(w)_x in J1 = horn ▸ w, where w sits after the horn tops.
    Fw : Nat → Tm
    Fw x = ev Θ (snd (nth ([] , v 0) xs x)) [ ⟪ map var (range pre) ++ (var (pre + nΓ) ∷ []) ⟫ ]tm

    J2tbl : List (Maybe Tm)
    J2tbl = front ++ concatMap (λ x → map (λ j →
              if j <ℕ (n + n) then bnd x j
              else if j ==ℕ (n + n) then just (var (pre + x))
              else if j ==ℕ suc (n + n) then just (Fw x) else nothing)
              (range (3 + (n + n)))) (range nΓ)

    J2 : Maybe Ctx
    J2 = horn >>= λ H → trCtx (suc n) >>= λ T → just (fst (inst (fst H ▸ wTy) T (nth nothing J2tbl)))

    marks : List Nat
    marks = mk horn
      where
      isVar′ : Tm → List Nat
      isVar′ (var j) = j ∷ []
      isVar′ _       = []
      mk : Maybe (Ctx × List Tm) → List Nat
      mk nothing  = []
      mk (just H) = concatMap (λ l → isVar′ (nth (var 0) (snd H) l)) (trMarked n)

  hornGen : Nat → Maybe HornData
  hornGen n = stage n >>= λ S →
    At.J2 n S >>= λ J → just (hd J (suc ((n + n) + nΓ)) (At.marks n S))

-- The horn shape at (Γ, n) for every n, Γ globular of dimension ≤ 1.
hornDataGen : Ctx → Nat → Maybe HornData
hornDataGen Γ n = if dimLe 1 Γ then (toExCtx Γ >>= λ E → Gen.hornGen Γ E n) else nothing

-- The horn shapes: every n over diagrams of dimension ≤ 1 (the cylinder
-- lifts), and n = 0 over 2-dimensional diagrams (the hand-built F(u)_α).
-- n ≥ 1 over a 2-dimensional diagram needs F(w)_α, the naturality of the
-- 3-cell F(u)_α in the 1-cell u (depth 2), which the lifts of
-- CaTTExp.Cones do not cover.
hornData : Ctx → Nat → Maybe HornData
hornData Γ n = if dimLe 1 Γ then hornDataGen Γ n
               else if n ==ℕ 0 then hornDataHand Γ 0 else nothing
