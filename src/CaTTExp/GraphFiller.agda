------------------------------------------------------------------------
-- The discreteness filler for graph contexts (open-issues F2).
--
-- A *graph context* is a pure CaTT context whose entries all have type
-- ⋆ (vertices) or ⋆-arrows between variables (edges). The free weak
-- ω-category on a graph is equivalent to the free category on it
-- (notes/conjectures/free-on-graph.md, solved), so two parallel cells
-- of the same "path" should always be connected by a cell. This module
-- builds that cell as a single CaTT coherence over a chain pasting
-- context Θ_k, following the researcher's canonical lift by position
-- along the path (DFMRV Prop. 7.19 and 7.32):
--
--   fill Γ u v  =  coh Θ_k (lift u →_{lift A} lift v) [σ_p]
--
-- where p is the common path of u and v, k its length, σ_p : Θ_k → Γ
-- picks the vertices and edges of p in order, and `lift` re-reads a
-- term of Γ inside Θ_k by giving every occurrence of an edge the
-- position it has along the path.
--
-- The construction is a *tactic*: it produces raw syntax, and the
-- certified checker (CaTTExp.Check) decides whether the result is a
-- well-typed cell u → v. So every filler it returns comes with a
-- genuine derivation, and no new typing rule is involved. Totality (that
-- it succeeds on every parallel pair of the same path) is the paper
-- theorem in notes/ordinary-math.md §3; here it is checked on examples
-- (CaTTExp.GraphFillerExamples). Lift functions run on fuel, since they
-- recurse into substitutions; fuel exhaustion only makes the tactic fail,
-- never makes it unsound.
------------------------------------------------------------------------
module CaTTExp.GraphFiller where

open import CaTTExp.Prelude
open import CaTTExp.Pure

------------------------------------------------------------------------
-- Small list and number helpers.

private
  length : ∀ {a} {A : Set a} → List A → Nat
  length []       = 0
  length (_ ∷ xs) = suc (length xs)

  replicate : ∀ {a} {A : Set a} → Nat → A → List A
  replicate zero    _ = []
  replicate (suc n) x = x ∷ replicate n x

  sum : List Nat → Nat
  sum []       = 0
  sum (n ∷ ns) = n + sum ns

  -- Monadic map over lists.
  mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → Maybe B) → List A → Maybe (List B)
  mapM f []       = just []
  mapM f (x ∷ xs) = f x >>= λ y → mapM f xs >>= λ ys → just (y ∷ ys)

  concatM : List (List Nat) → List Nat
  concatM []         = []
  concatM (xs ∷ xss) = xs ++ concatM xss

  listEq : List Nat → List Nat → Bool
  listEq []       []       = true
  listEq (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ listEq xs ys
  listEq _        _        = false

------------------------------------------------------------------------
-- The chain pasting context Θ_k = (v₀ —e₁→ v₁ —e₂→ … —e_k→ v_k).
-- Levels: v₀ = 0, v_i = 2i − 1 and e_i = 2i for i ≥ 1.

chain : Nat → Ctx
chain k = ctxOf (node (replicate k leaf))

vtx : Nat → Nat
vtx zero    = 0
vtx (suc i) = suc (i + i)        -- 2(i+1) − 1

edge : Nat → Nat                 -- the i-th edge, counted from 1
edge i = i + i

------------------------------------------------------------------------
-- Reading a graph context.

isVertex : Ctx → Nat → Bool
isVertex Γ i with lookup Γ i
... | just ⋆ = true
... | _      = false

------------------------------------------------------------------------
-- Inside a pasting context Θ (as used by a coh): the object variables
-- and edges. In a ps-context every non-initial object y at level ℓ is
-- immediately followed, at level ℓ+1, by an edge into y whose source is
-- an earlier object (rule pse with A = ⋆).

-- The 0-dimensional iterated source of a type, when it is a variable.
src₀Ty : Ty → Maybe Nat
src₀Ty ⋆                    = nothing
src₀Ty (arr ⋆ (var a) _)    = just a
src₀Ty (arr ⋆ _ _)          = nothing
src₀Ty (arr (arr B s t) _ _) = src₀Ty (arr B s t)

-- The object of Θ "at the left" of variable j: j itself for objects,
-- the iterated 0-source otherwise.
src₀Var : Ctx → Nat → Maybe Nat
src₀Var Θ j with lookup Θ j
... | just ⋆           = just j
... | just (arr B s t) = src₀Ty (arr B s t)
... | nothing          = nothing

------------------------------------------------------------------------
-- Paths. `pathTm fuel Γ t` is the list of edges (levels of Γ) of the
-- strict image of a 1-dimensional term t, in order. For a coh over a
-- 1-dimensional pasting context (a chain) it concatenates the paths of
-- the arguments at the chain's edges; over the one-point context it is
-- empty (an identity).

mutual
  pathTm : Nat → Ctx → Tm → Maybe (List Nat)
  pathTm zero    Γ t = nothing
  pathTm (suc n) Γ (var i) = if isVertex Γ i then nothing else just (i ∷ [])
  pathTm (suc n) Γ (coh Θ (arr ⋆ _ _) τ) = chainPath n Γ Θ τ 1 (len Θ)
  pathTm (suc n) Γ (coh Θ _ τ) = nothing   -- only 1-dimensional terms here
  pathTm (suc n) Γ (cst ())

  -- Walk the edges e₁, e₂, … of Θ while they exist (Θ must be a chain
  -- or a point), concatenating the paths of their images.
  chainPath : Nat → Ctx → Ctx → Sub → Nat → Nat → Maybe (List Nat)
  chainPath n Γ Θ τ i zero = just []
  chainPath n Γ Θ τ i (suc fuel) =
    if len Θ <ℕ suc (edge i)            -- no edge e_i: we are done
    then just []
    else (pathTm n Γ (lookupₛ τ (edge i)) >>= λ p →
          chainPath n Γ Θ τ (suc i) fuel >>= λ ps →
          just (p ++ ps))

-- The 1-dimensional iterated source of a type of dimension ≥ 1, and its
-- 0-dimensional source.
src₁ : Ty → Maybe (Tm × Ty)       -- the 1-cell and its type (arr ⋆ a b)
src₁ ⋆                     = nothing
src₁ (arr ⋆ s t)           = nothing  -- a type of 1-cells has no 1-cell source
src₁ (arr (arr ⋆ a b) s t) = just (s , arr ⋆ a b)
src₁ (arr (arr (arr B a b) c d) s t) = src₁ (arr (arr B a b) c d)

-- The path of a cell t : A of dimension ≥ 1 (A of dimension ≥ 1), and
-- the vertex where it starts.
cellPath : Nat → Ctx → Tm → Ty → Maybe (List Nat × Nat)
cellPath n Γ t (arr ⋆ (var a) b) = pathTm n Γ t >>= λ p → just (p , a)
cellPath n Γ t (arr ⋆ _ b)       = nothing
cellPath n Γ t ⋆                 = nothing
cellPath n Γ t (arr (arr B c d) s s') =
  src₁ (arr (arr B c d) s s') >>= λ where
    (u , arr ⋆ (var a) _) → pathTm n Γ u >>= λ p → just (p , a)
    _ → nothing

------------------------------------------------------------------------
-- Lifting. `liftTm fuel Γ t o` re-reads the Γ-term t inside a chain
-- context, with t's path starting at position o.

mutual
  liftTm : Nat → Ctx → Tm → Nat → Maybe Tm
  liftTm zero    Γ t o = nothing
  liftTm (suc n) Γ (var i) o =
    just (if isVertex Γ i then var (vtx o) else var (edge (suc o)))
  liftTm (suc n) Γ (coh Θ A τ) o =
    liftSub n Γ Θ τ o (len Θ) >>= λ τ' → just (coh Θ A τ')
  liftTm (suc n) Γ (cst ()) o

  -- Lift each argument of a coh over Θ at the offset of its 0-source
  -- object. Builds the substitution entry by entry (left to right).
  liftSub : Nat → Ctx → Ctx → Sub → Nat → Nat → Maybe Sub
  liftSub n Γ Θ τ o zero = just ⟨⟩
  liftSub n Γ Θ τ o (suc j) =
    liftSub n Γ Θ τ o j >>= λ τ' →
    src₀Var Θ j >>= λ x →
    offObj n Γ Θ τ x (suc x) >>= λ off →
    liftTm n Γ (lookupₛ τ j) (o + off) >>= λ t' →
    just (τ' ,ₛ t')

  -- The offset of the object at level x of Θ: the total length of the
  -- paths of the images of the edges leading to it along the spine.
  offObj : Nat → Ctx → Ctx → Sub → Nat → Nat → Maybe Nat
  offObj n Γ Θ τ x zero = nothing
  offObj n Γ Θ τ zero (suc f) = just 0
  offObj n Γ Θ τ (suc x) (suc f) with lookup Θ (suc (suc x))
  ... | just (arr ⋆ (var y) _) =
        offObj n Γ Θ τ y f >>= λ oy →
        pathTm n Γ (lookupₛ τ (suc (suc x))) >>= λ p →
        just (oy + length p)
  ... | _ = nothing

-- Lift a type. The 0-dimensional target of a cell of path length k
-- sits at position o + k.
liftTy : Nat → Ctx → Ty → Nat → Nat → Maybe Ty
liftTy n Γ ⋆ o k = just ⋆
liftTy n Γ (arr ⋆ a b) o k =
  liftTm n Γ a o >>= λ a' → liftTm n Γ b (o + k) >>= λ b' → just (arr ⋆ a' b')
liftTy n Γ (arr (arr B c d) s t) o k =
  liftTy n Γ (arr B c d) o k >>= λ B' →
  liftTm n Γ s o >>= λ s' → liftTm n Γ t o >>= λ t' → just (arr B' s' t')

------------------------------------------------------------------------
-- The substitution σ_p : Θ_k → Γ for a path p starting at vertex a.

-- The target vertex of edge e of Γ.
edgeTgt : Ctx → Nat → Maybe Nat
edgeTgt Γ e with lookup Γ e
... | just (arr ⋆ _ (var b)) = just b
... | _ = nothing

pathSub : Ctx → Nat → List Nat → Maybe Sub
pathSub Γ a p = go (⟨⟩ ,ₛ var a) p
  where
  go : Sub → List Nat → Maybe Sub
  go σ []       = just σ
  go σ (e ∷ es) = edgeTgt Γ e >>= λ b → go (σ ,ₛ var b ,ₛ var e) es

------------------------------------------------------------------------
-- The tactic: a raw candidate filler, then certification.

-- Enough fuel for any term the tactic meets: the fuel bounds recursion
-- depth, and every recursive call descends into a strictly smaller term.
-- A generous constant keeps typechecking of examples fast.
fuel : Nat
fuel = 64

fillRaw : Ctx → Tm → Tm → Ty → Maybe Tm
fillRaw Γ u v A =
  cellPath fuel Γ u A >>= λ { (p , a) →
  cellPath fuel Γ v A >>= λ { (q , b) →
  guard (listEq p q ∧ (a ==ℕ b)) λ _ →
  liftTy fuel Γ A 0 (length p) >>= λ A' →
  liftTm fuel Γ u 0 >>= λ u' →
  liftTm fuel Γ v 0 >>= λ v' →
  pathSub Γ a p >>= λ σ →
  just (coh (chain (length p)) (arr A' u' v') σ) } }

-- Certified filler: if it returns, the result is a derivation of
-- Γ ⊢ fill ∶ u →_A v in plain CaTT.
fill : (Γ : Ctx) (u v : Tm) (A : Ty) → Maybe (Σ Tm (λ c → Γ ⊢tm c ∶ arr A u v))
fill Γ u v A =
  fillRaw Γ u v A >>= λ c →
  infer Γ c >>= λ { (B , d) → cast B c d (B ==Ty arr A u v) (==Ty-sound B (arr A u v)) }
  where
  cast : ∀ B c → Γ ⊢tm c ∶ B → (b : Bool) → (T b → B ≡ arr A u v) →
         Maybe (Σ Tm (λ c → Γ ⊢tm c ∶ arr A u v))
  cast B c d true  eq = just (c , subst (Γ ⊢tm c ∶_) (eq tt) d)
  cast B c d false _  = nothing
