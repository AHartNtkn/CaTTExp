------------------------------------------------------------------------
-- The discreteness filler for globular contexts (open-issues F2b).
--
-- A *globular context* is a pure CaTT context in which the source and
-- target of every variable are variables (e.g. x, s : x → x,
-- α : s ⇒ s). By the free-on-graph theorem (notes/ordinary-math.md
-- §3.3, Thm 3.2), two parallel cells of such a Γ with the same image in
-- the free *strict* ω-category on Γ are connected by a single coherence
--
--   fill Γ u v A  =  coh Θ_τ (ũ →_Ã ṽ) [λ]
--
-- where (τ, λ) is the common strict image: a pasting tree τ (a Batanin
-- tree) with a labelling λ of its cells by variables of Γ, Θ_τ is the
-- pasting context of τ, and ũ, ṽ, Ã re-read u, v, A inside Θ_τ, giving
-- every variable occurrence the cell of τ it occupies.
--
-- Strict normal forms are labelled trees (`LT`): `lt os cs` is a
-- pasting diagram whose 0-cells are labelled os = o₀ … oₘ and whose
-- i-th hom (between oᵢ₋₁ and oᵢ) is the diagram cs[i], one dimension
-- up. A k-composite a ∗ₖ b merges the trees (`merge`); the image of
-- coh_{Θ,A}[σ] is the composite of Θ's tree with each locally maximal
-- variable y replaced by the image of σ(y) (`nf`, `flat`). Since Γ is
-- globular, the image of a variable is its globe. Identities need no
-- extra constructor: a cell and its identity have the same tree.
--
-- The lift runs the same recursion with *position trees*: labelled
-- trees whose labels are variables of Θ_τ. Splitting a position tree
-- along a composite (`split`) gives each argument σ(y) the cells it
-- occupies.
--
-- This is a *tactic* with certified output, as CaTTExp.GraphFiller:
-- the candidate is raw syntax, and the certified checker decides
-- whether it is a well-typed cell u → v. Every filler it returns is a
-- theorem of plain CaTT, whatever the correctness of the normal-form
-- code. Recursion into substitutions runs on fuel, set to one more
-- than the coh-nesting depth of the inputs. That this is always enough
-- is not proved here; it is part of the open totality item F2c. Totality is the paper theorem (Thm 3.2); it
-- is checked here on examples (CaTTExp.GlobularFillerExamples).
------------------------------------------------------------------------
module CaTTExp.GlobularFiller where

open import CaTTExp.Prelude
open import CaTTExp.Pure

------------------------------------------------------------------------
-- List helpers (in a named module, so proofs can refer to them).

module Lists where
  length : ∀ {a} {A : Set a} → List A → Nat
  length []       = 0
  length (_ ∷ xs) = suc (length xs)

  take drop : ∀ {a} {A : Set a} → Nat → List A → List A
  take zero    _        = []
  take (suc n) []       = []
  take (suc n) (x ∷ xs) = x ∷ take n xs
  drop zero    xs       = xs
  drop (suc n) []       = []
  drop (suc n) (_ ∷ xs) = drop n xs

  headN lastN : List Nat → Nat
  headN []      = 0
  headN (x ∷ _) = x
  lastN []           = 0
  lastN (x ∷ [])     = x
  lastN (_ ∷ y ∷ ys) = lastN (y ∷ ys)

  listEq : List Nat → List Nat → Bool
  listEq []       []       = true
  listEq (x ∷ xs) (y ∷ ys) = (x ==ℕ y) ∧ listEq xs ys
  listEq _        _        = false

  find : ∀ {a} {A : Set a} → Nat → List (Nat × A) → Maybe A
  find n []             = nothing
  find n ((m , a) ∷ xs) = if n ==ℕ m then just a else find n xs

open Lists

------------------------------------------------------------------------
-- Labelled pasting trees.

data LT : Set where
  lt : List Nat → List LT → LT

mutual
  shape : LT → Tree
  shape (lt _ cs) = node (shapes cs)

  shapes : List LT → List Tree
  shapes []       = []
  shapes (c ∷ cs) = shape c ∷ shapes cs

mutual
  ltEq : LT → LT → Bool
  ltEq (lt os cs) (lt os' cs') = listEq os os' ∧ ltEqs cs cs'

  ltEqs : List LT → List LT → Bool
  ltEqs []       []       = true
  ltEqs (c ∷ cs) (d ∷ ds) = ltEq c d ∧ ltEqs cs ds
  ltEqs _        _        = false

-- a ∗ₖ b, for a and b sharing their k-boundary.
mutual
  merge : Nat → LT → LT → LT
  merge zero    (lt os cs) (lt os' cs') = lt (os ++ drop 1 os') (cs ++ cs')
  merge (suc k) (lt os cs) (lt _   cs') = lt os (mergeL k cs cs')

  mergeL : Nat → List LT → List LT → List LT
  mergeL k (a ∷ as) (b ∷ bs) = merge k a b ∷ mergeL k as bs
  mergeL k _        _        = []

-- The k-dimensional source (false) or target (true).
mutual
  bd : Bool → Nat → LT → LT
  bd false zero    (lt os cs) = lt (headN os ∷ []) []
  bd true  zero    (lt os cs) = lt (lastN os ∷ []) []
  bd b     (suc k) (lt os cs) = lt os (bdL b k cs)

  bdL : Bool → Nat → List LT → List LT
  bdL b k []       = []
  bdL b k (c ∷ cs) = bd b k c ∷ bdL b k cs

-- Split a tree of shape a ∗ₖ b into its a- and b-parts, given a.
mutual
  split : Nat → LT → LT → LT × LT
  split zero (lt _ csA) (lt os cs) =
    lt (take (suc m) os) (take m cs) , lt (drop m os) (drop m cs)
    where m = length csA
  split (suc k) (lt _ csA) (lt os cs) with splitL k csA cs
  ... | (as , bs) = lt os as , lt os bs

  splitL : Nat → List LT → List LT → List LT × List LT
  splitL k (a ∷ as) (c ∷ cs) with split k a c | splitL k as cs
  ... | (x , y) | (xs , ys) = x ∷ xs , y ∷ ys
  splitL k _ _ = [] , []

-- The label of the top cell of a globe.
top : LT → Nat
top (lt os [])      = headN os
top (lt _ (c ∷ _))  = top c

------------------------------------------------------------------------
-- The tree of a pasting context, labelled by its own variables.
-- The numbering follows CaTTExp.PastingTrees.build: each child of a
-- node adds its target object y (level n) and its cell f (level n+1),
-- and f is the first 0-cell of the child's hom.

mutual
  labT : Tree → Nat → Nat → LT × Nat
  labT (node cs) x n with labCs cs n
  ... | (os , ls , n') = lt (x ∷ os) ls , n'

  labCs : List Tree → Nat → List Nat × List LT × Nat
  labCs []       n = [] , [] , n
  labCs (c ∷ cs) n with labT c (suc n) (suc (suc n))
  ... | (l , n₁) with labCs cs n₁
  ...   | (os , ls , n₂) = n ∷ os , l ∷ ls , n₂

idTree : Tree → LT
idTree τ = fst (labT τ 0 1)

-- Pair the labels of two trees of the same shape.
mutual
  zipLab : LT → LT → List (Nat × Nat)
  zipLab (lt os cs) (lt os' cs') = zipN os os' ++ zipLabs cs cs'

  zipLabs : List LT → List LT → List (Nat × Nat)
  zipLabs (c ∷ cs) (d ∷ ds) = zipLab c d ++ zipLabs cs ds
  zipLabs _        _        = []

  zipN : List Nat → List Nat → List (Nat × Nat)
  zipN (x ∷ xs) (y ∷ ys) = (x , y) ∷ zipN xs ys
  zipN _        _        = []

------------------------------------------------------------------------
-- Strict normal forms.

-- The globe of a variable of type A.
wrap : Ty → LT → Maybe LT
wrap ⋆                         t = just t
wrap (arr B (var a) (var b))   t = wrap B (lt (a ∷ b ∷ []) (t ∷ []))
wrap (arr _ _ _)               t = nothing

mutual
  nf : Nat → Ctx → Tm → Maybe LT
  nf zero    Γ _             = nothing
  nf (suc n) Γ (var x)       = lookup Γ x >>= λ A → wrap A (lt (x ∷ []) [])
  nf (suc n) Γ (coh Θ A σ)   = treeOf Θ >>= λ τ → flat n Γ σ 0 (idTree τ)
  nf (suc n) Γ (cst _)       = nothing

  -- The composite of a labelled pasting diagram of Θ, at depth d,
  -- with each locally maximal variable y replaced by the image of σ(y).
  flat : Nat → Ctx → Sub → Nat → LT → Maybe LT
  flat n Γ σ d (lt (y ∷ []) [])   = nf n Γ (lookupₛ σ y)
  flat n Γ σ d (lt _ [])          = nothing
  flat n Γ σ d (lt _ (c ∷ cs))    = flatL n Γ σ d c cs

  flatL : Nat → Ctx → Sub → Nat → LT → List LT → Maybe LT
  flatL n Γ σ d c []        = flat n Γ σ (suc d) c
  flatL n Γ σ d c (c' ∷ cs) =
    flat n Γ σ (suc d) c >>= λ a →
    flatL n Γ σ d c' cs  >>= λ b →
    just (merge d a b)

------------------------------------------------------------------------
-- The lift: re-read a term inside Θ_τ, given the cells it occupies.

mutual
  liftT : Nat → Ctx → Tm → LT → Maybe Tm
  liftT zero    Γ _             E = nothing
  liftT (suc n) Γ (var x)       E = just (var (top E))
  liftT (suc n) Γ (coh Θ A σ)   E =
    treeOf Θ >>= λ τ →
    assign n Γ σ 0 (idTree τ) E >>= λ as →
    liftS n Γ σ as (len Θ) >>= λ σ′ →
    just (coh Θ A σ′)
  liftT (suc n) Γ (cst _)       E = nothing

  -- The lifted arguments, in order of level.
  liftS : Nat → Ctx → Sub → List (Nat × LT) → Nat → Maybe Sub
  liftS n Γ σ as zero    = just ⟨⟩
  liftS n Γ σ as (suc i) =
    liftS n Γ σ as i >>= λ s →
    find i as >>= λ E →
    liftT n Γ (lookupₛ σ i) E >>= λ t →
    just (s ,ₛ t)

  -- The position tree of every variable of Θ, from that of the
  -- composite (E), walking Θ's labelled tree at depth d.
  assign : Nat → Ctx → Sub → Nat → LT → LT → Maybe (List (Nat × LT))
  assign n Γ σ d (lt (y ∷ []) []) E = just ((y , E) ∷ [])
  assign n Γ σ d (lt _ [])        E = nothing
  assign n Γ σ d (lt os (c ∷ cs)) E = assignCs n Γ σ d os c cs E

  assignCs : Nat → Ctx → Sub → Nat → List Nat → LT → List LT → LT →
             Maybe (List (Nat × LT))
  assignCs n Γ σ d (o ∷ o' ∷ []) c [] E =
    assign n Γ σ (suc d) c E >>= λ as →
    just ((o , bd false d E) ∷ (o' , bd true d E) ∷ as)
  assignCs n Γ σ d (o ∷ os) c (c' ∷ cs) E =
    flat n Γ σ (suc d) c >>= λ a →
    go (split d a E)
    where
    go : LT × LT → Maybe (List (Nat × LT))
    go (Ea , Eb) =
      assign n Γ σ (suc d) c Ea >>= λ as →
      assignCs n Γ σ d os c' cs Eb >>= λ bs →
      just (((o , bd false d Ea) ∷ as) ++ bs)
  assignCs n Γ σ d _ c _ E = nothing

liftTy : Nat → Ctx → Ty → LT → Maybe Ty
liftTy n Γ ⋆           E = just ⋆
liftTy n Γ (arr B a b) E =
  liftTy n Γ B (bd false (dim B) E) >>= λ B′ →
  liftT n Γ a (bd false (dim B) E) >>= λ a′ →
  liftT n Γ b (bd true  (dim B) E) >>= λ b′ →
  just (arr B′ a′ b′)

------------------------------------------------------------------------
-- The substitution λ : Θ_τ → Γ.

labSub : List (Nat × Nat) → Nat → Maybe Sub
labSub ls zero    = just ⟨⟩
labSub ls (suc i) = labSub ls i >>= λ s → find i ls >>= λ x → just (s ,ₛ var x)

------------------------------------------------------------------------
-- The tactic.

-- Fuel: one more than the coh-nesting depth of the inputs. nf, flat,
-- liftT and assign spend one unit exactly when they enter the
-- arguments of a coh, and liftTy is structural in the type, so this
-- fuel is meant never to run out (unproved; part of F2c). There is no
-- fixed bound on the size of u, v, A.
mutual
  depthTm : Tm → Nat
  depthTm (var _)     = 0
  depthTm (coh _ _ σ) = suc (depthSub σ)
  depthTm (cst _)     = 0

  depthSub : Sub → Nat
  depthSub ⟨⟩       = 0
  depthSub (σ ,ₛ t) = max (depthSub σ) (depthTm t)

depthTy : Ty → Nat
depthTy ⋆           = 0
depthTy (arr A t u) = max (depthTy A) (max (depthTm t) (depthTm u))

fuelFor : Tm → Tm → Ty → Nat
fuelFor u v A = suc (max (depthTy A) (max (depthTm u) (depthTm v)))

-- The common strict image of u and v, if they have one.
image : Nat → Ctx → Tm → Tm → Maybe LT
image fuel Γ u v =
  nf fuel Γ u >>= λ Nu →
  nf fuel Γ v >>= λ Nv →
  guard (ltEq Nu Nv) λ _ → just Nu

fillRaw : Ctx → Tm → Tm → Ty → Maybe Tm
fillRaw Γ u v A =
  let fuel = fuelFor u v A in
  image fuel Γ u v >>= λ N →
  let τ = shape N ; I = idTree τ ; Θ = ctxOf τ in
  liftTy fuel Γ A I >>= λ A′ →
  liftT fuel Γ u I >>= λ u′ →
  liftT fuel Γ v I >>= λ v′ →
  labSub (zipLab I N) (len Θ) >>= λ λσ →
  just (coh Θ (arr A′ u′ v′) λσ)

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
