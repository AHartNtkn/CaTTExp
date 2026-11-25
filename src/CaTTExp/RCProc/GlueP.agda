------------------------------------------------------------------------
-- Glue cells over pasting trees, with typed terms throughout (ledger
-- S20 (i), stage 4c; notes/rc-generator.md §1, stage 4 plan).
--
-- A glue cell of the strips (tools/rc_descent.py `_gcoh`) is a cell
-- a ⇛ b between two composites of the variables of a small pasting
-- context P = ctxOf T, instantiated at cells of Γ.  Here:
--   * P's variables are typed terms of P (`varT`, from P ⊢ctx, which
--     every tree gives: `treeCtx`);
--   * the caller builds a and b from them with the decided composition
--     of RCProc.TypedOps, so a and b are typed terms of P;
--   * the substitution P → Γ is computed by unification from the
--     images of some variables (untrusted, `unify`), the boundaries of
--     a typed cell being typed by inversion (`bdT`), and then typed by
--     RCProc.TypedSub.buildSub (the only decided facts are syntactic
--     equalities of types);
--   * the cell is answered by rcP on P and pulled back (glueCell).
-- Every `just` is a typed term of Γ.  Also: vertical composition of
-- typed cells with a decided junction (`transT?`).
------------------------------------------------------------------------
module CaTTExp.RCProc.GlueP where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ty; ps-wf)
open import CaTTExp.RCProc.Glue using (Ans; transA)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (decTm)
open import CaTTExp.RCProc.DescentGlue using (glueCell)

psCtx : ∀ {Γ} → Γ ⊢ps → Γ ⊢ctx
psCtx (ps d) = fst (ps-wf d)

treeCtx : (T : Tree) → ctxOf T ⊢ctx
treeCtx T = psCtx (snd (psOf T))

-- The variable at level i, typed.
varT : ∀ {Γ} → Γ ⊢ctx → Nat → Maybe (TTm Γ)
varT {Γ} w i = go (lookup Γ i) refl
  where
  go : (m : Maybe Ty) → lookup Γ i ≡ m → Maybe (TTm Γ)
  go nothing  _ = nothing
  go (just A) e = just tt[ var i ∶ A , var-wf w e ]

-- The source and target of a typed cell, typed (by inversion).
bdT : ∀ {Γ} → TTm Γ → Maybe (TTm Γ × TTm Γ)
bdT x = go (ty x) (tm-ty (der x))
  where
  go : ∀ {Γ} (A : Ty) → Γ ⊢ty A → Maybe (TTm Γ × TTm Γ)
  go ⋆           _                = nothing
  go (arr B s t) (arr-wf ds dt)   = just (tt[ s ∶ B , ds ] , tt[ t ∶ B , dt ])

-- Vertical composite of two typed cells, the junction decided.
transT? : ∀ {Γ} → TTm Γ → TTm Γ → Maybe (TTm Γ)
transT? {Γ} c h = go (ty c) (der c) (ty h) (der h)
  where
  go : (C : Ty) → Γ ⊢tm tm c ∶ C → (H : Ty) → Γ ⊢tm tm h ∶ H → Maybe (TTm Γ)
  go (arr A t s) dc (arr A′ s′ u) dh =
    decTy A′ A >>= λ p → decTm s′ s >>= λ q →
    let r = transA (tm c , dc)
              (tm h , subst (Γ ⊢tm tm h ∶_)
                        (cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) p (cong₂ _,_ q refl)) dh)
    in just tt[ fst r ∶ arr A t u , snd r ]
  go _ _ _ _ = nothing

-- Untrusted unification: images of P's variables from the images of
-- some of them (an association list level ↦ typed term of Γ), by
-- reading boundaries from the highest level down.  The result is only
-- a candidate: buildSub decides it.
private
  get : ∀ {a} {X : Set a} → List (Nat × X) → Nat → Maybe X
  get []             i = nothing
  get ((j , x) ∷ xs) i = if i ==ℕ j then just x else get xs i

  down : ∀ {Γ} → Ctx → Nat → List (Nat × TTm Γ) → List (Nat × TTm Γ)
  down P zero    m = m
  down P (suc i) m = down P i (step (lookup P i) (get m i))
    where
    step : Maybe Ty → Maybe (TTm _) → List (Nat × TTm _)
    step (just (arr _ (var a) (var b))) (just x) with bdT x
    ... | just (s , t) = (a , s) ∷ (b , t) ∷ m
    ... | nothing      = m
    step _ _ = m

  collect : ∀ {Γ} → Nat → List (Nat × TTm Γ) → Maybe (List (TTm Γ))
  collect zero    m = just []
  collect (suc n) m = collect n m >>= λ es → get m n >>= λ e → just (es ++ (e ∷ []))

unify : ∀ {Γ} → Γ ⊢ctx → (P : Ctx) → List (Nat × TTm Γ) → Maybe (TSub Γ P)
unify w P imgs = collect (len P) (down P (len P) imgs) >>= buildSub w P

-- The glue cell a ⇛ b over ctxOf T, at the images `imgs`; `ends`
-- builds a and b from the typed variables of P.
glueT : ∀ {Γ} → Γ ⊢ctx → (T : Tree) → List (Nat × TTm Γ) →
        ((Nat → Maybe (TTm (ctxOf T))) → Maybe (TTm (ctxOf T) × TTm (ctxOf T))) →
        Maybe (TTm Γ)
glueT {Γ} w T imgs ends =
  unify w P imgs >>= λ σ →
  ends (varT (treeCtx T)) >>= λ ab →
  go σ (fst ab) (snd ab)
  where
  P = ctxOf T
  go : TSub Γ P → TTm P → TTm P → Maybe (TTm Γ)
  go (σ , dσ) a b =
    decTy (ty b) (ty a) >>= λ p →
    glueCell (der a) (subst (P ⊢tm tm b ∶_) p (der b)) dσ >>= λ r →
    just tt[ fst r ∶ _ , snd r ]
