------------------------------------------------------------------------
-- Machine checks for CaTTExp.Cones. Every `_ = refl` below runs the
-- certified checker of CaTTExp.Check at typechecking time: `ok K`
-- evaluates to true only if `checkCtx` returns a typing derivation of
-- the CaTT context K.
------------------------------------------------------------------------
module CaTTExp.ConesExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones

ok : ExCtx → Bool
ok K = is-just (checkCtx (evCtx K))

okM : Maybe ExCtx → Bool
okM nothing  = false
okM (just K) = ok K

------------------------------------------------------------------------
-- Diagram shapes (all globular).

-- The n-disk: x, y, then the (source, target) pairs, then the top cell.
diskTy : Nat → ExTy
diskTy zero    = ob
diskTy (suc j) = hom (diskTy j) (v (j + j)) (v (suc (j + j)))

DiskEx : Nat → ExCtx
DiskEx n = concatMap (λ j → diskTy j ∷ diskTy j ∷ []) (range n) ++ (diskTy n ∷ [])

-- x → y
Arr : ExCtx
Arr = DiskEx 1

-- A loop with a 2-cell on it: x, f : x → x, α : f ⇒ f
-- (the shape of the researcher's counterexample to arbitrary cones).
Loop : ExCtx
Loop = ob ∷ hom ob (v 0) (v 0) ∷ hom (hom ob (v 0) (v 0)) (v 1) (v 1) ∷ []

-- Two parallel 2-cells α, β : f ⇒ g (not a pasting context).
Par2 : ExCtx
Par2 = DiskEx 2 ++ (hom (hom ob (v 0) (v 1)) (v 2) (v 3) ∷ [])

-- A cospan x → z ← y (pullback shape).
Cospan : ExCtx
Cospan = ob ∷ ob ∷ ob ∷ hom ob (v 0) (v 2) ∷ hom ob (v 1) (v 2) ∷ []

-- A parallel pair f, g : x → y (equalizer shape).
PPair : ExCtx
PPair = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ hom ob (v 0) (v 1) ∷ []

-- An endo-arrow s : x → x (the ℕ-like shape).
Endo : ExCtx
Endo = ob ∷ hom ob (v 0) (v 0) ∷ []

-- A composable pair x → y → z.
Chain2 : ExCtx
Chain2 = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ ob ∷ hom ob (v 1) (v 3) ∷ []

-- A 3-cell between parallel 2-cells over a loop.
Loop3 : ExCtx
Loop3 = Loop ++ (hom (hom ob (v 0) (v 0)) (v 1) (v 1)
               ∷ hom (hom (hom ob (v 0) (v 0)) (v 1) (v 1)) (v 2) (v 3) ∷ [])

shapes : List ExCtx
shapes = DiskEx 0 ∷ DiskEx 1 ∷ DiskEx 2 ∷ DiskEx 3 ∷ DiskEx 4
       ∷ Loop ∷ Par2 ∷ Cospan ∷ PPair ∷ Endo ∷ Chain2 ∷ Loop3 ∷ []

-- The shapes are well-formed CaTT contexts, and globular.
_ : all ok shapes ≡ true
_ = refl
_ : all globular shapes ≡ true
_ = refl

------------------------------------------------------------------------
-- 1. The specified cone is a well-formed context for every shape.

_ : all (λ Γ → ok (ConeOf.cone Γ)) shapes ≡ true
_ = refl

-- ... and is admitted by Mikhail's printed (KE) rule: the free-variable
-- conditions τCond, σCond and linearity hold for every projection.
okKE : ExCtx → Bool
okKE Γ = KE.okConeAll (evCtx (ConeOf.cone Γ)) (length Γ)

_ : all okKE shapes ≡ true
_ = refl

------------------------------------------------------------------------
-- 2. The specified cocone.

_ : all (λ Γ → ok (CoconeOf.cocone Γ)) shapes ≡ true
_ = refl

------------------------------------------------------------------------
-- 3. Suspensions and constant-diagram instances of the cocone.

_ : all (λ Γ → ok (susp Γ)) shapes ≡ true
_ = refl

_ : all (λ Γ → ok (constCocone Γ)) shapes ≡ true
_ = refl

------------------------------------------------------------------------
-- 4. Gray cylinders I ⊗ Γ of globular contexts (all variables moved).

grayΓ : ExCtx → Maybe ExCtx
grayΓ Γ = CylOf.cyl Γ (range (length Γ)) >>= λ C → just (Cyl.ctx C)

_ : all (λ Γ → okM (grayΓ Γ)) shapes ≡ true
_ = refl

------------------------------------------------------------------------
-- 5. Conical transfors ctrf_k over 1-dimensional shapes, k = 1, 2, 3.

oneDim : List ExCtx
oneDim = DiskEx 0 ∷ DiskEx 1 ∷ Cospan ∷ PPair ∷ Endo ∷ Chain2 ∷ []

okCtrf : Nat → ExCtx → Bool
okCtrf k Γ with ctrf k Γ
... | nothing = false
... | just T  = ok (Ctrf.ctx T)

ctrfDefined : Nat → ExCtx → Bool
ctrfDefined k Γ with ctrf k Γ
... | nothing = false
... | just _  = true

_ : all (okCtrf 1) oneDim ≡ true
_ = refl
_ : all (okCtrf 2) oneDim ≡ true
_ = refl
_ : all (okCtrf 3) oneDim ≡ true
_ = refl

------------------------------------------------------------------------
-- 6. Negative and boundary checks (so that the checks above are not
--    vacuous).

-- The checker rejects an ill-typed context.
_ : ok (ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ hom (hom ob (v 0) (v 1)) (v 2) (v 0) ∷ []) ≡ false
_ = refl

-- (KE) rejects a projection whose target forgets the arrow: over x → y,
-- p_f : p_y ⇒ p_y (instead of p_y ⇒ p_x ∗₀ f). The context is well typed,
-- so the rejection is (KE)'s, not the type checker's.
badCone : ExCtx
badCone = Arr ++ (ob ∷ hom ob (v 3) (v 0) ∷ hom ob (v 3) (v 1)
                 ∷ hom (hom ob (v 3) (v 1)) (v 5) (v 5) ∷ [])

_ : ok badCone ≡ true
_ = refl
_ : KE.okConeAll (evCtx badCone) 3 ≡ false
_ = refl

-- The researcher's non-canonical cone over the loop x, f : x → x,
-- α : f ⇒ f (notes/conjectures/lax-colimit-of-point.md §3): it reuses
-- the projection r = p_f twice. (KE) admits it, which is why the
-- judgment had to be replaced by a construction. Levels: x0 f1 α2 c3
-- q4 r5 b6, with r : q ⇒ q ∗₀ f and
--   s = r ∗₁ (r ∗₀ 1_f),  w = 1_{q∗₀f} ∗₀ α,  b : s ⇛ s ∗₁ w.
nonCanonical : ExCtx
nonCanonical = Loop ++ (ob ∷ hom ob (v 3) (v 0)
             ∷ hom (hom ob (v 3) (v 0)) (v 4) (bn 0 (v 4) (v 1))
             ∷ hom (tyE pre s) s (bn 1 s w) ∷ [])
  where
  s = bn 1 (v 5) (bn 0 (v 5) (idn (v 1)))
  w = bn 0 (idn (bn 0 (v 4) (v 1))) (v 2)
  pre = Loop ++ (ob ∷ hom ob (v 3) (v 0) ∷ hom (hom ob (v 3) (v 0)) (v 4) (bn 0 (v 4) (v 1)) ∷ [])

_ : ok nonCanonical ≡ true
_ = refl
_ : KE.okConeAll (evCtx nonCanonical) 3 ≡ true
_ = refl
-- It is not the specified cone (which is also well typed).
_ : ok (ConeOf.cone Loop) ≡ true
_ = refl
_ : nonCanonical ≡ ConeOf.cone Loop → ⊥
_ = λ ()

-- Depth 1 (ledger B18): over a 2-dimensional shape, ctrf₁ needs the
-- naturality of p_x ∗₀ α in p_x (an interchange coherence) and of
-- p_f ∗₁ (p_x ∗₀ α) (the pasting of m_f and that interchange through
-- associators). With those lifts, ctrf₁ is well typed on every
-- 2-dimensional shape of the suite, and so is the cocone version.
twoDim : List ExCtx
twoDim = DiskEx 2 ∷ Loop ∷ Par2 ∷ []

_ : all (okCtrf 1) twoDim ≡ true
_ = refl

-- The next level needs naturality of those coherences themselves
-- (depth 1 in a 3-dimensional coherence, BMOSV), which is not
-- implemented: the lift returns nothing and no context is produced.
_ : ctrfDefined 2 (DiskEx 2) ≡ false
_ = refl

-- Over a 3-dimensional shape even ctrf₁ needs depth-2 lifts (p_x ∗₀ θ
-- for a 3-cell θ), which are not implemented.
_ : ctrfDefined 1 (DiskEx 3) ≡ false
_ = refl

module Show where
  ctrf1Arr ctrf2Arr : Maybe Ctrf
  ctrf1Arr = ctrf 1 Arr
  ctrf2Arr = ctrf 2 Arr

-- Marking: ctrf₁ over x → y marks m_f only; ctrf₂ marks m⁻_f, m⁺_f, μ_f.
_ : (ctrf 1 Arr >>= λ T → just (Ctrf.marked T)) ≡ just (12 ∷ [])
_ = refl
_ : (ctrf 2 Arr >>= λ T → just (Ctrf.marked T)) ≡ just (16 ∷ 17 ∷ 18 ∷ [])
_ = refl

------------------------------------------------------------------------
-- 7. Duality: the cocone is the O_odd-dual of the cone of the dual
--    diagram (a syntactic identity, not just a check).

_ : all (λ Γ → ok (dualCtx Γ)) shapes ≡ true
_ = refl

okCoctrf : Nat → ExCtx → Bool
okCoctrf k Γ with coctrf k Γ
... | nothing = false
... | just T  = ok (Ctrf.ctx T)

_ : all (okCoctrf 1) oneDim ≡ true
_ = refl
_ : all (okCoctrf 2) oneDim ≡ true
_ = refl
-- Cocone transfors over 2-dimensional shapes (B18), via the duals of
-- the interchange and associator lifts.
_ : all (okCoctrf 1) (DiskEx 2 ∷ Loop ∷ Par2 ∷ []) ≡ true
_ = refl

------------------------------------------------------------------------
-- 8. Free object = lax colimit of the point, for 1-dimensional shapes.

okCylK : ExCtx → Bool
okCylK Γ with CylOf.cyl (constCocone Γ) (rangeFrom 2 (length Γ))
... | nothing = false
... | just C  = ok (Cyl.ctx C)

okConst : ExCtx → Bool
okConst Γ = ConstPoint.okφ Γ ∧ ConstPoint.okψ Γ ∧ ConstPoint.okH Γ ∧ ConstPoint.okH′ Γ

_ : okConst Arr ≡ true
_ = refl
_ : all okConst oneDim ≡ true
_ = refl

-- Dimension 2 (ledger B20): ψ (cocone ⇒ family) and the homotopy
-- H : ψφ ≃ id on the family side, on every shape of dimension ≤ 2.
-- The cocone-side homotopy H′ is open; its cylinder is built and well
-- typed (the lift of id²_⊤ ∗₀ q_y is the reversed interchange).
_ : all (λ Γ → ConstD2.okψ Γ ∧ ConstD2.okH Γ) (twoDim ++ oneDim) ≡ true
_ = refl
_ : all (λ Γ → okCylK Γ) twoDim ≡ true
_ = refl

-- Non-vacuity: the naive identification q ↦ s is not a substitution
-- ΣΓ → K (q_f's target is id_⊤ ∗₀ q_y, not q_y), so φ has real content.
_ : is-just (checkCtx (ConstPoint.ΣΓ Arr) >>= λ w →
             checkSub (ConstPoint.ΣΓ Arr) w (idₛ (ConstPoint.ΣΓ Arr)) (ConstPoint.𝒦 Arr)) ≡ false
_ = refl

-- The directly-defined cocone is literally the O_odd-dual of the cone
-- of the O_odd-dual diagram.
_ : map CoconeOf.cocone shapes ≡ map (λ Γ → dualCtx (ConeOf.cone (dualCtx Γ))) shapes
_ = refl

-- φ (a family is a cocone) for every shape, in every dimension.
_ : all PhiAll.okφ shapes ≡ true
_ = refl
-- On 1-dimensional shapes it is the φ of ConstPoint.
_ : map PhiAll.φ oneDim ≡ map ConstPoint.φ oneDim
_ = refl

------------------------------------------------------------------------
-- 9. A non-globular diagram: τ : f ∗₀ g ⇒ h (boundary is a composite).
--    Its cone needs the cone cell over the composite f ∗₀ g:
--      P(f ∗₀ g) := (p_g ∗₁ (p_f ∗₀ g)) ∗₁ κ,
--    κ : (p_x ∗₀ f) ∗₀ g ⇒ p_x ∗₀ (f ∗₀ g), the associator over the
--    chain c → x → y → z (notes/specified-cones.md §5, Prop. 5.2).
--    Levels: x0 y1 f2 z3 g4 h5 τ6 | c7 p_x8 p_y9 p_f10 p_z11 p_g12 p_h13 p_τ14.

module NonGlobular where
  open import CaTTExp.Prelude
  Tri : ExCtx
  Tri = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ ob ∷ hom ob (v 1) (v 3)
      ∷ hom ob (v 0) (v 3) ∷ hom (hom ob (v 0) (v 3)) (bn 0 (v 2) (v 4)) (v 5) ∷ []

  -- The cone up to p_h, which only needs variable boundaries.
  pre : ExCtx
  pre = Tri ++ (ob ∷ hom ob (v 7) (v 0) ∷ hom ob (v 7) (v 1)
       ∷ hom (hom ob (v 7) (v 1)) (v 9) (bn 0 (v 8) (v 2))
       ∷ hom ob (v 7) (v 3)
       ∷ hom (hom ob (v 7) (v 3)) (v 11) (bn 0 (v 9) (v 4))
       ∷ hom (hom ob (v 7) (v 3)) (v 11) (bn 0 (v 8) (v 5)) ∷ [])

  C₀ : Ctx
  C₀ = evCtx pre
  g : Nat → Cell
  g = gen C₀

  Chain3 : Ctx
  Chain3 = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))
  -- In Chain3 (a0 b1 u2 d3 w4 e5 r6): (u ∗₀ w) ∗₀ r ⇒ u ∗₀ (w ∗₀ r).
  assocT : Ty
  assocT = arr (snd l) (fst l) (fst r)
    where
    l = binC 0 (binC 0 (gen Chain3 2) (gen Chain3 4)) (gen Chain3 6)
    r = binC 0 (gen Chain3 2) (binC 0 (gen Chain3 4) (gen Chain3 6))
  κ : Cell
  κ = coh Chain3 assocT ⟪ fst (g 7) ∷ fst (g 0) ∷ fst (g 8) ∷ fst (g 1) ∷ fst (g 2) ∷ fst (g 3) ∷ fst (g 4) ∷ [] ⟫
    , assocT [ ⟪ fst (g 7) ∷ fst (g 0) ∷ fst (g 8) ∷ fst (g 1) ∷ fst (g 2) ∷ fst (g 3) ∷ fst (g 4) ∷ [] ⟫ ]ty

  Pfg : Cell
  Pfg = binC 1 (binC 1 (g 12) (binC 0 (g 10) (g 4))) κ

  pτTy : Ty
  pτTy = arr (snd (g 13)) (var 13) (fst (binC 1 Pfg (binC 0 (g 8) (g 6))))

  cone : Ctx
  cone = C₀ ▸ pτTy

  _ : is-just (checkCtx cone) ≡ true
  _ = refl
  -- Mikhail's (KE) admits it too.
  _ : KE.okConeAll cone 7 ≡ true
  _ = refl
