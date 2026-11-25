------------------------------------------------------------------------
-- A check of RCProc.Descent.Piece by evaluation, with one moved
-- generator.  Γ is the chain x —f→ y —g→ z —k→ w (levels x0 y1 f2 z3
-- g4 w5 k6), p = (f ;₀ g) ;₀ k and q = f ;₀ (g ;₀ k).  The query is
-- t = u = 1_p (the glue cell p ⇛ p).  The plan: W the 1-disc
-- x —h→ w, the generators x, w, p (p not expanded), R p = h and
-- J h = q.  So p moves (p⁺ = q), its bridge p ⇛ q is a recursive call,
-- the squares of 1_p have fillers from the direct (op) fillers, and the
-- top whisker p↑ of a_t is stripped by stripR.  The answer has type
-- 1_p ⇛ 1_p, decided.  A plan whose J is ill typed gives nothing.
------------------------------------------------------------------------
module CaTTExp.RCProc.Descent.PieceExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc using (rcS; Ans)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; ansT)
open import CaTTExp.RCProc.GlueP using (treeCtx; varT)
open import CaTTExp.RCProc.Strip using (gcoh; Ends)
open import CaTTExp.RCProc.Descent.Lift using (FillO)
open import CaTTExp.RCProc.Descent.LiftOp using (FillOpO; fillDirectOp)
open import CaTTExp.RCProc.Descent.Fill using (RecAll; fillC)
open import CaTTExp.RCProc.Descent.Piece

private
  T₃ : Tree
  T₃ = node (leaf ∷ leaf ∷ leaf ∷ [])

  Γ : Ctx
  Γ = ctxOf T₃

  wΓ : Γ ⊢ctx
  wΓ = treeCtx T₃

  W : Tree
  W = node (leaf ∷ [])

  wW : ctxOf W ⊢ctx
  wW = treeCtx W

  v : Nat → Maybe (TTm Γ)
  v = varT wΓ

  pM qM : Maybe (TTm Γ)
  pM = v 2 >>= λ f → v 4 >>= λ g → v 6 >>= λ k → rcomp? 0 0 f g >>= λ fg → rcomp? 0 0 fg k
  qM = v 2 >>= λ f → v 4 >>= λ g → v 6 >>= λ k → rcomp? 0 0 g k >>= λ gk → rcomp? 0 0 f gk

  p q x w : TTm Γ
  p = from-just pM
  q = from-just qM
  x = from-just (v 0)
  w = from-just (v 5)

  plain : Ends
  plain _ (y ∷ _) = just y
  plain _ []      = nothing

  -- 1_p : p ⇛ p, a coherence over the 1-disc applied to x, w, p
  oneP : TTm Γ
  oneP = from-just (gcoh wΓ 0 (p ∷ []) plain plain)

  recS : RecAll
  recS {Δ} _ a b = decTy (ty b) (ty a) >>= λ e →
                   rcS (der a) (subst (Δ ⊢tm tm b ∶_) e (der b)) >>= λ r → just (ansT r)

  F : FillO
  F = fillC 4 recS

  G : FillOpO
  G = fillDirectOp F recS

  isVar : Tm → Bool
  isVar (var _) = true
  isVar _       = false

  Rof : TTm Γ → Maybe (TTm (ctxOf W))
  Rof y = if tm y ==Tm var 0 then varT wW 0
          else if tm y ==Tm var 5 then varT wW 1
          else if tm y ==Tm tm p then varT wW 2
          else nothing

  plan : List (TTm Γ) → Plan Γ
  plan J = record { tree = W
                  ; exp  = λ t → not (isVar t) ∧ not (t ==Tm tm p)
                  ; Jimg = J
                  ; Rimg = Rof
                  ; gens = x ∷ w ∷ p ∷ [] }

  ans : List (TTm Γ) → Maybe (Ans Γ (ty oneP) (tm oneP) (tm oneP))
  ans J = pieceA wΓ recS F G (plan J) (der oneP) (der oneP)

-- p and q differ, so p moves
_ : tm p ==Tm tm q ≡ false
_ = refl

_ : is-just (ans (x ∷ w ∷ q ∷ [])) ≡ true
_ = refl

-- J sending h to a cell of the wrong type: no answer
_ : is-just (ans (x ∷ w ∷ from-just (v 2) ∷ [])) ≡ false
_ = refl

-- one bridge (for p) and no reversed bridge (p is not top-dimensional)
private
  size : ∀ {X : Set} → List X → Nat
  size []       = 0
  size (_ ∷ xs) = suc (size xs)

  counts : Maybe (Nat × Nat)
  counts = buildSub wΓ (ctxOf W) (x ∷ w ∷ q ∷ []) >>= λ J →
           tables wΓ recS F G (plan (x ∷ w ∷ q ∷ [])) J 2 (x ∷ w ∷ p ∷ []) (tabs [] [] []) >>= λ tb →
           just (size (tUp tb) , size (tDn tb))

_ : counts ≡ just (1 , 0)
_ = refl

------------------------------------------------------------------------
-- The same piece with the descent itself as the recursion oracle and
-- its fillers (Descent.RcD, with no further plans), and rcD on the query.

open import CaTTExp.RCProc.Descent.RcD using (PlanO; rcDT; rcD)
open import CaTTExp.RCProc.Descent.LiftOp using (fillDirectOp)

private
  noPlan : PlanO
  noPlan _ _ _ = nothing

  r : RecAll
  r = rcDT 4 noPlan

_ : is-just (pieceA wΓ r (fillC 3 r) (fillDirectOp (fillC 3 r) r) (plan (x ∷ w ∷ q ∷ [])) (der oneP) (der oneP)) ≡ true
_ = refl

_ : is-just (rcD 4 noPlan wΓ (der oneP) (der oneP)) ≡ true
_ = refl
