------------------------------------------------------------------------
-- Strictly unital (and associative) CaTT (ledger item D16): the
-- reduction relation of CaTT_su (Finster–Reutter–Vicary–Rice, "A type theory for strictly
-- unital ∞-categories", LICS 2022) on raw syntax, a normaliser, and a
-- certified equality test.
--
-- The rules (one step, plus congruence everywhere):
--
--   disc   coh (Dₙ₊₁) (Uₙ₊₁) σ          ⟶  the top term of σ
--          (the unary composite on a disc is its argument);
--   endo   coh Γ (s →_A s) σ             ⟶  id (A[σ]) (s[σ])
--          (an endo-coherence is the identity on its source);
--   prune  coh Γ A σ                     ⟶  coh (Γ//f) (A[π_f]) (σ//f)
--          when f is a locally maximal variable of the ps-context Γ
--          and σ(f) is an identity. Γ//f removes f : x → y and its
--          target y; π_f sends y ↦ x, f ↦ id x, and renumbers.
--   insert coh ⌊S⌋ A σ                   ⟶  coh ⌊S ≪_P T⌋ (A[κ]) (σ ≪_P τ)
--          when σ labels a branch P of S by the standard coherence
--          Cⁿ_T[τ] (n = lh P, bh P ≤ th T, dim T ≤ n): the insertion
--          rule of CaTT_sua (Finster–Rice–Vicary, "A syntax for
--          strictly associative and unital ∞-categories", Defs. 18–29).
--          Identities are standard coherences C^{n+1}_{Dⁿ}, so this
--          also inserts identities. Deviation from the paper (argued,
--          not formalised): κ sends the whole branch disc to
--          {Uⁿ_T, Cⁿ_T}[ι] in one step instead of by the recursive
--          suspension Σκ; the two agree because suspension commutes
--          with standard types and coherences.
--          The insert constructor is defined through insertAt, so its
--          agreement with FRV Defs. 18–29 holds by construction of
--          insertAt plus the checked examples (CaTTExp.SUExamples); it
--          is not proved.
--
-- Here Dₙ is the n-disc context, Uₙ the type of its top variable, and
-- id A s = coh Dₙ (dₙ → dₙ) ⟨A, s⟩ with n = dim A.
--
-- The relation is stated on raw terms; CaTT_su applies it to well-typed
-- terms, where an identity in σ(f) is automatically the identity on
-- σ(x). `nf` is one strategy (bottom-up, then disc, endo, prune at the
-- head, then insertion, repeated) with a fuel bound; it returns a reduction sequence.
-- `_==su_` compares normal forms and is sound for this relation: a
-- positive answer gives a common reduct under ⟶*. It is not claimed
-- complete.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.SU (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.PastingCheck 𝕊 using (checkPs)
open import CaTTExp.PastingTrees 𝕊 using (Tree; node; ctxOf; treeOf)

------------------------------------------------------------------------
-- Discs and identities.

Uᵈ : Nat → Ty
Uᵈ zero    = ⋆
Uᵈ (suc n) = arr (Uᵈ n) (var (n + n)) (var (suc (n + n)))

Dᵈ : Nat → Ctx
Dᵈ zero    = ε ▸ ⋆
Dᵈ (suc n) = Dᵈ n ▸ Uᵈ n ▸ Uᵈ (suc n)

-- The substitution Dₙ → Γ given by a term s : A (n = dim A).
discS : Ty → Tm → Sub
discS ⋆           s = ⟨⟩ ,ₛ s
discS (arr A a b) s = discS A a ,ₛ b ,ₛ s

idTm : Ty → Tm → Tm
idTm A s = coh (Dᵈ (dim A)) (arr (Uᵈ (dim A)) (var (dim A + dim A)) (var (dim A + dim A))) (discS A s)

isId : Tm → Bool
isId (coh Γ (arr B s u) _) =
  let n = dim B in (Γ ==Ctx Dᵈ n) ∧ (B ==Ty Uᵈ n) ∧ (s ==Tm var (n + n)) ∧ (u ==Tm var (n + n))
isId _ = false

lastₛ : Sub → Tm
lastₛ ⟨⟩       = var 0
lastₛ (_ ,ₛ t) = t

------------------------------------------------------------------------
-- Contexts and substitutions as lists (oldest first).

private
  [_] : ∀ {a} {A : Set a} → A → List A
  [ x ] = x ∷ []

  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  take drop : ∀ {a} {A : Set a} → Nat → List A → List A
  take zero    _        = []
  take (suc n) []       = []
  take (suc n) (x ∷ xs) = x ∷ take n xs
  drop zero    xs       = xs
  drop (suc n) []       = []
  drop (suc n) (x ∷ xs) = drop n xs

  nth : ∀ {a} {A : Set a} → Nat → List A → Maybe A
  nth n       []       = nothing
  nth zero    (x ∷ _)  = just x
  nth (suc n) (_ ∷ xs) = nth n xs

  concatMap : ∀ {a} {A : Set a} {B : Set} → (A → List B) → List A → List B
  concatMap f []       = []
  concatMap f (x ∷ xs) = f x ++ concatMap f xs

  -- n, n+1, …, n+k−1
  range : Nat → Nat → List Nat
  range n zero    = []
  range n (suc k) = n ∷ range (suc n) k

ctxL : Ctx → List Ty
ctxL ε       = []
ctxL (Γ ▸ A) = ctxL Γ ++ [ A ]

fromL : List Ty → Ctx
fromL = go ε
  where
  go : Ctx → List Ty → Ctx
  go Γ []       = Γ
  go Γ (A ∷ As) = go (Γ ▸ A) As

subL : Sub → List Tm
subL ⟨⟩       = []
subL (σ ,ₛ t) = subL σ ++ [ t ]

fromSL : List Tm → Sub
fromSL = go ⟨⟩
  where
  go : Sub → List Tm → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ t) ts

------------------------------------------------------------------------
-- Pruning at position y (y is the target, f = y + 1 the variable).

private
  -- The source x and type B of f : x →_B y, if f has that shape.
  fShape : Ctx → Nat → Maybe (Nat × Ty)
  fShape Γ y with nth (suc y) (ctxL Γ)
  ... | just (arr B (var x) (var y′)) = guard (y′ ==ℕ y) λ _ → just (x , B)
  ... | _                             = nothing

pruneSub : Ctx → Nat → Sub
pruneSub Γ y with fShape Γ y
... | just (x , B) =
  fromSL (map var (range 0 y) ++ (var x ∷ idTm B (var x) ∷ map var (range y (len Γ ∸ (y + 2)))))
... | nothing = idₛ Γ

pruneCtx : Ctx → Nat → Ctx
pruneCtx Γ y = fromL (take y (ctxL Γ) ++ map (_[ pruneSub Γ y ]ty) (drop (y + 2) (ctxL Γ)))

dropSub : Sub → Nat → Sub
dropSub σ y = fromSL (take y (subL σ) ++ drop (y + 2) (subL σ))

prunable : Ctx → Sub → Nat → Bool
prunable Γ σ y with fShape Γ y
... | nothing = false
... | just _  =
  is-just (checkPs Γ)
  ∧ not (elem (suc y) (concatMap fvTy (drop (y + 2) (ctxL Γ))))
  ∧ isId (lookupₛ σ (suc y))


------------------------------------------------------------------------
-- Insertion (CaTT_sua, Finster–Rice–Vicary, "A syntax for strictly
-- associative and unital ∞-categories", Defs. 18–23, 29).
--
-- Trees are Batanin trees, `node [T₁ … Tₙ]`, with context ⌊T⌋ =
-- ⋁ Σ⌊Tᵢ⌋ (`ctxOf`). A labelling of T is `lab s₀ [(L₁, s₁) … (Lₙ, sₙ)]`:
-- the objects s₀ … sₙ and a labelling Lᵢ of each Tᵢ. In ⌊T⌋ the
-- variables come in the order s₀, s₁, ⌊T₁⌋, s₂, ⌊T₂⌋, …, so labellings
-- and substitutions convert by `flat` / `unf`. Child indices are
-- 0-based here (1-based in the paper).

data Lab : Set where
  lab : Tm → List (Lab × Tm) → Lab

mutual
  flat : Lab → List Tm
  flat (lab s ps) = s ∷ flatPs ps

  flatPs : List (Lab × Tm) → List Tm
  flatPs []             = []
  flatPs ((L , s) ∷ ps) = s ∷ (flat L ++ flatPs ps)

mutual
  unf : Tree → List Tm → Lab × List Tm
  unf (node ts) []       = lab (var 0) [] , []
  unf (node ts) (s ∷ r)  = let (ps , r′) = unfPs ts r in lab s ps , r′

  unfPs : List Tree → List Tm → List (Lab × Tm) × List Tm
  unfPs []       r       = [] , r
  unfPs (t ∷ ts) []      = [] , []
  unfPs (t ∷ ts) (s ∷ r) =
    let (L , r′)   = unf t r
        (ps , r″) = unfPs ts r′
    in ((L , s) ∷ ps) , r″

toSub : Lab → Sub
toSub L = fromSL (flat L)

idLab : Tree → Lab
idLab T = fst (unf T (map var (range 0 (len (ctxOf T)))))

private
  length : ∀ {a} {A : Set a} → List A → Nat
  length []       = 0
  length (_ ∷ xs) = suc (length xs)

  maxL : List Nat → Nat
  maxL []       = 0
  maxL (n ∷ ns) = max n (maxL ns)

  children : Tree → List Tree
  children (node ts) = ts

  nthOr : ∀ {a} {A : Set a} → A → Nat → List A → A
  nthOr d n xs with nth n xs
  ... | just x  = x
  ... | nothing = d

  leafT : Tree
  leafT = node []

mutual
  dimT : Tree → Nat
  dimT (node []) = 0
  dimT (node ts) = suc (maxL (dimTs ts))

  dimTs : List Tree → List Nat
  dimTs []       = []
  dimTs (t ∷ ts) = dimT t ∷ dimTs ts

-- Trunk height.
th : Tree → Nat
th (node (t ∷ [])) = suc (th t)
th _               = 0

linear : Tree → Bool
linear T = th T ==ℕ dimT T

-- Boundary tree ∂ⁿT, and the source/target inclusions δ^{±,n} as
-- labellings of ∂ⁿT by terms of ⌊T⌋.
bdry : Nat → Tree → Tree
bdry zero    _         = node []
bdry (suc n) (node ts) = node (go ts)
  where
  go : List Tree → List Tree
  go []       = []
  go (t ∷ ts) = bdry n t ∷ go ts

private
  lastObj : Lab → Tm
  lastObj (lab s ps) = go s ps
    where
    go : Tm → List (Lab × Tm) → Tm
    go s []             = s
    go s ((_ , x) ∷ ps) = go x ps

truncL : Bool → Nat → Lab → Lab
truncL plus zero    L          = lab (if plus then lastObj L else first L) []
  where
  first : Lab → Tm
  first (lab s _) = s
truncL plus (suc n) (lab s ps) = lab s (go ps)
  where
  go : List (Lab × Tm) → List (Lab × Tm)
  go []             = []
  go ((L , x) ∷ ps) = (truncL plus n L , x) ∷ go ps

-- Standard types Uⁿ_T and standard terms Tⁿ_T (Def. 4).
mutual
  stdTy : Nat → Tree → Ty
  stdTy zero    T = ⋆
  stdTy (suc n) T =
    arr (stdTy n T)
        (stdTm n (bdry n T) [ toSub (truncL false n (idLab T)) ]tm)
        (stdTm n (bdry n T) [ toSub (truncL true  n (idLab T)) ]tm)

  stdTm : Nat → Tree → Tm
  stdTm n T = if linear T ∧ (dimT T ==ℕ n) then var (n + n) else stdCoh n T

  stdCoh : Nat → Tree → Tm
  stdCoh n T = coh (ctxOf T) (stdTy n T) (idₛ (ctxOf T))

-- Disc labellings: {A, s} as a labelling of the linear tree of dim A.
dlab : Ty → Tm → Lab
dlab ⋆           s = lab s []
dlab (arr A a b) s = deepen (dlab A a)
  where
  deepen : Lab → Lab
  deepen (lab x [])            = lab x ((lab s [] , b) ∷ [])
  deepen (lab x ((L , y) ∷ _)) = lab x ((deepen L , y) ∷ [])

-- Branches: non-empty paths to linear subtrees.
mutual
  branches : Tree → List (List Nat)
  branches (node ts) = brs 0 ts

  brs : Nat → List Tree → List (List Nat)
  brs k []       = []
  brs k (t ∷ ts) =
    (if linear t then (k ∷ []) ∷ [] else []) ++ map (k ∷_) (branches t) ++ brs (suc k) ts

-- Leaf height lh(P) and the label ⌊P⌋ of a branch.
lh : Tree → List Nat → Nat
lh (node ts) (k ∷ [])     = suc (dimT (nthOr leafT k ts))
lh (node ts) (k ∷ P)      = suc (lh (nthOr leafT k ts) P)
lh _         []           = 0

private
  innermost : Lab → Tm
  innermost (lab s [])            = s
  innermost (lab s ((L , _) ∷ _)) = innermost L

  dummy : Lab × Tm
  dummy = lab (var 0) [] , var 0

labAt : Lab → List Nat → Tm
labAt (lab s ps) (k ∷ [])    = innermost (fst (nthOr dummy k ps))
labAt (lab s ps) (k ∷ P)     = labAt (fst (nthOr dummy k ps)) P
labAt (lab s _)  []          = s

-- S ≪_P T on trees and on labellings.
insT : Tree → List Nat → Tree → Tree
insT (node ss) (k ∷ [])    (node ts) = node (take k ss ++ ts ++ drop (suc k) ss)
insT (node ss) (k ∷ P)     T         =
  node (take k ss ++ insT (nthOr leafT k ss) P (nthOr leafT 0 (children T)) ∷ drop (suc k) ss)
insT S         []          _         = S

insL : Lab → List Nat → Lab → Lab
insL (lab s ps) (k ∷ [])    (lab t qs) = lab s (take k ps ++ qs ++ drop (suc k) ps)
insL (lab s ps) (k ∷ P)     (lab t qs) =
  let (Lk , sk) = nthOr dummy k ps in
  lab s (take k ps ++ (insL Lk P (fst (nthOr dummy 0 qs)) , sk) ∷ drop (suc k) ps)
insL L          []          _          = L

-- ι : the part of ⌊S ≪_P T⌋'s labelling I that is the inserted T.
private
  objBefore : Nat → Tm → List (Lab × Tm) → Tm
  objBefore zero    s _  = s
  objBefore (suc k) s ps = snd (nthOr (lab s [] , s) k ps)

iota : Lab → List Nat → Tree → Lab
iota (lab s ps) (k ∷ [])    (node ts) = lab (objBefore k s ps) (take (length ts) (drop k ps))
iota (lab s ps) (k ∷ P)     T         =
  let (L′ , s′) = nthOr dummy k ps in
  lab (objBefore k s ps) ((iota L′ P (nthOr leafT 0 (children T)) , s′) ∷ [])
iota L          []          _         = L

-- κ : the labelling of S by ⌊S ≪_P T⌋: the identity off the branch, and
-- the disc of the branch sent to {Uⁿ_T, Cⁿ_T}[ι] (n = lh P).
kappaGo : Lab → Tree → List Nat → Nat → Lab → Lab
kappaGo (lab s ps) (node ss) (k ∷ [])    m (lab _ qs) =
  lab s (take k ps ++ nthOr dummy 0 qs ∷ drop (k + m) ps)
kappaGo (lab s ps) (node ss) (k ∷ P)     m (lab _ qs) =
  let (L′ , s′) = nthOr dummy k ps in
  lab s (take k ps ++ (kappaGo L′ (nthOr leafT k ss) P m (fst (nthOr dummy 0 qs)) , s′) ∷ drop (suc k) ps)
kappaGo I          _         []          _ _          = I

-- The number of children of the innermost tree inserted at the base.
private
  baseWidth : List Nat → Tree → Nat
  baseWidth (_ ∷ [])  (node ts) = length ts
  baseWidth (_ ∷ P)   T         = baseWidth P (nthOr leafT 0 (children T))
  baseWidth []        _         = 0

-- The insertion step, if (S, P, T) is an insertion redex at branch P
-- of coh Γ A σ (Γ = ⌊S⌋). Returns the reduct.
insertAt : Ctx → Ty → Sub → List Nat → Maybe Tm
insertAt Γ A σ P with treeOf Γ
... | nothing = nothing
... | just S  = go (labAt (fst (unf S (subL σ))) P)
  where
  withT : Ctx → Ty → Sub → Tree → Maybe Tm
  withT Δ U ρ T =
    let n  = lh S P
        ok = (ctxOf S ==Ctx Γ) ∧ (ctxOf T ==Ctx Δ) ∧ (U ==Ty stdTy n T)
             ∧ (length P <ℕ suc (suc (th T))) ∧ (dimT T <ℕ suc n)
        I  = idLab (insT S P T)
        ι  = toSub (iota I P T)
        κ  = toSub (kappaGo I S P (baseWidth P T) (dlab (stdTy n T [ ι ]ty) (coh (ctxOf T) (stdTy n T) ι)))
    in if ok
       then just (coh (ctxOf (insT S P T)) (A [ κ ]ty)
                      (toSub (insL (fst (unf S (subL σ))) P (fst (unf T (subL ρ))))))
       else nothing

  go : Tm → Maybe Tm
  go (coh Δ U ρ) with treeOf Δ
  ... | just T  = withT Δ U ρ T
  ... | nothing = nothing
  go _ = nothing

------------------------------------------------------------------------
-- The reduction relation.

infix 4 _⟶_ _⟶ty_ _⟶s_
mutual
  data _⟶_ : Tm → Tm → Set where
    disc  : ∀ n σ → coh (Dᵈ (suc n)) (Uᵈ (suc n)) σ ⟶ lastₛ σ
    endo  : ∀ Γ A s σ → coh Γ (arr A s s) σ ⟶ idTm (A [ σ ]ty) (s [ σ ]tm)
    prune : ∀ Γ A σ y → T (prunable Γ σ y) →
            coh Γ A σ ⟶ coh (pruneCtx Γ y) (A [ pruneSub Γ y ]ty) (dropSub σ y)
    insert : ∀ Γ A σ P t → insertAt Γ A σ P ≡ just t → coh Γ A σ ⟶ t
    cohA  : ∀ {Γ A A′ σ} → A ⟶ty A′ → coh Γ A σ ⟶ coh Γ A′ σ
    cohσ  : ∀ {Γ A σ σ′} → σ ⟶s σ′ → coh Γ A σ ⟶ coh Γ A σ′

  data _⟶ty_ : Ty → Ty → Set where
    arrA : ∀ {A A′ t u} → A ⟶ty A′ → arr A t u ⟶ty arr A′ t u
    arrt : ∀ {A t t′ u} → t ⟶ t′ → arr A t u ⟶ty arr A t′ u
    arru : ∀ {A t u u′} → u ⟶ u′ → arr A t u ⟶ty arr A t u′

  data _⟶s_ : Sub → Sub → Set where
    headₛ : ∀ {σ t t′} → t ⟶ t′ → (σ ,ₛ t) ⟶s (σ ,ₛ t′)
    tailₛ : ∀ {σ σ′ t} → σ ⟶s σ′ → (σ ,ₛ t) ⟶s (σ′ ,ₛ t)

-- Reflexive–transitive closure.
infixr 5 _◅_
data Star {A : Set} (R : A → A → Set) : A → A → Set where
  ε* : ∀ {x} → Star R x x
  _◅_ : ∀ {x y z} → R x y → Star R y z → Star R x z

_⟶*_ : Tm → Tm → Set
_⟶*_ = Star _⟶_

_⟶ty*_ : Ty → Ty → Set
_⟶ty*_ = Star _⟶ty_

_⟶s*_ : Sub → Sub → Set
_⟶s*_ = Star _⟶s_

_◅◅_ : ∀ {A} {R : A → A → Set} {x y z} → Star R x y → Star R y z → Star R x z
ε*       ◅◅ q = q
(r ◅ p) ◅◅ q = r ◅ (p ◅◅ q)

gmap : ∀ {A B : Set} {R : A → A → Set} {S : B → B → Set} (f : A → B) →
       (∀ {x y} → R x y → S (f x) (f y)) → ∀ {x y} → Star R x y → Star S (f x) (f y)
gmap f g ε*      = ε*
gmap f g (r ◅ p) = g r ◅ gmap f g p

-- Congruence of many-step reduction.
coh* : ∀ {Γ A A′ σ σ′} → A ⟶ty* A′ → σ ⟶s* σ′ → coh Γ A σ ⟶* coh Γ A′ σ′
coh* {Γ} {A} {A′} {σ} {σ′} p q =
  gmap (λ X → coh Γ X σ) cohA p ◅◅ gmap (λ s → coh Γ A′ s) cohσ q

arr* : ∀ {A A′ t t′ u u′} → A ⟶ty* A′ → t ⟶* t′ → u ⟶* u′ → arr A t u ⟶ty* arr A′ t′ u′
arr* {A} {A′} {t} {t′} {u} {u′} p q r =
  gmap (λ X → arr X t u) arrA p ◅◅ (gmap (λ s → arr A′ s u) arrt q ◅◅ gmap (λ s → arr A′ t′ s) arru r)

ext* : ∀ {σ σ′ t t′} → σ ⟶s* σ′ → t ⟶* t′ → (σ ,ₛ t) ⟶s* (σ′ ,ₛ t′)
ext* {σ} {σ′} {t} {t′} p q = gmap (λ s → s ,ₛ t) tailₛ p ◅◅ gmap (λ s → σ′ ,ₛ s) headₛ q

------------------------------------------------------------------------
-- One head step, if any (identities are left alone).

private
  check : (b : Bool) → Maybe (T b)
  check true  = just tt
  check false = nothing

  firstPrune : (Γ : Ctx) (σ : Sub) → Nat → Nat → Maybe (Σ Nat λ y → T (prunable Γ σ y))
  firstPrune Γ σ y zero    = nothing
  firstPrune Γ σ y (suc k) with check (prunable Γ σ y)
  ... | just p  = just (y , p)
  ... | nothing = firstPrune Γ σ (suc y) k

  tryDisc : (Γ : Ctx) (A : Ty) (σ : Sub) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
  tryDisc Γ ⋆           σ = nothing
  tryDisc Γ (arr B a b) σ with check (Γ ==Ctx Dᵈ (suc (dim B))) | check (arr B a b ==Ty Uᵈ (suc (dim B)))
  ... | just p | just q =
    just (lastₛ σ , subst (λ X → coh X (arr B a b) σ ⟶ lastₛ σ) (sym (==Ctx-sound _ _ p))
                     (subst (λ Y → coh (Dᵈ (suc (dim B))) Y σ ⟶ lastₛ σ) (sym (==Ty-sound _ _ q))
                       (disc (dim B) σ)))
  ... | _ | _ = nothing

  tryEndo : (Γ : Ctx) (A : Ty) (σ : Sub) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
  tryEndo Γ ⋆           σ = nothing
  tryEndo Γ (arr B s u) σ with check (s ==Tm u)
  ... | just p = just (_ , subst (λ X → coh Γ (arr B s X) σ ⟶ idTm (B [ σ ]ty) (s [ σ ]tm))
                                  (==Tm-sound s u p) (endo Γ B s σ))
  ... | nothing = nothing

  tryPrune : (Γ : Ctx) (A : Ty) (σ : Sub) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
  tryPrune Γ A σ with firstPrune Γ σ 0 (len Γ)
  ... | just (y , p) = just (_ , prune Γ A σ y p)
  ... | nothing      = nothing

  tryInsertP : (Γ : Ctx) (A : Ty) (σ : Sub) → List (List Nat) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
  tryInsertP Γ A σ []       = nothing
  tryInsertP Γ A σ (P ∷ Ps) with insertAt Γ A σ P in e
  ... | just t  = just (t , insert Γ A σ P t e)
  ... | nothing = tryInsertP Γ A σ Ps

  tryInsert : (Γ : Ctx) (A : Ty) (σ : Sub) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
  tryInsert Γ A σ with treeOf Γ
  ... | just S  = tryInsertP Γ A σ (branches S)
  ... | nothing = nothing

  orElse : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
  orElse (just x) _ = just x
  orElse nothing  m = m

headStep : (Γ : Ctx) (A : Ty) (σ : Sub) → Maybe (Σ Tm λ t → coh Γ A σ ⟶ t)
headStep Γ A σ with isId (coh Γ A σ) | tryEndo Γ A σ
... | true  | _ = nothing
... | false | e = orElse (tryDisc Γ A σ) (orElse e (orElse (tryPrune Γ A σ) (tryInsert Γ A σ)))

-- Endo-coherence removal of a term that is already an identity gives
-- back the same term (for disc-shaped σ), so `headStep` skips
-- identities; this is what keeps `nf` from looping on id (id x).

------------------------------------------------------------------------
-- The normaliser: fuel bounds the number of head steps along any
-- branch; running out of fuel is safe (the result is still a reduct).

mutual
  nf : Nat → (t : Tm) → Σ Tm (t ⟶*_)
  nf n (var i)     = var i , ε*
  nf n (cst k)     = cst k , ε*
  nf n (coh Γ A σ) =
    let (A′ , p) = nfTy n A
        (σ′ , q) = nfSub n σ
        (v  , r) = headNf n Γ A′ σ′
    in v , (coh* p q ◅◅ r)

  nfTy : Nat → (A : Ty) → Σ Ty (A ⟶ty*_)
  nfTy n ⋆           = ⋆ , ε*
  nfTy n (arr A t u) =
    let (A′ , p) = nfTy n A
        (t′ , q) = nf n t
        (u′ , r) = nf n u
    in arr A′ t′ u′ , arr* p q r

  nfSub : Nat → (σ : Sub) → Σ Sub (σ ⟶s*_)
  nfSub n ⟨⟩       = ⟨⟩ , ε*
  nfSub n (σ ,ₛ t) =
    let (σ′ , p) = nfSub n σ
        (t′ , q) = nf n t
    in (σ′ ,ₛ t′) , ext* p q

  headNf : Nat → (Γ : Ctx) (A : Ty) (σ : Sub) → Σ Tm (coh Γ A σ ⟶*_)
  headNf zero    Γ A σ = coh Γ A σ , ε*
  headNf (suc n) Γ A σ with headStep Γ A σ
  ... | nothing      = coh Γ A σ , ε*
  ... | just (t , r) = let (v , rs) = nf n t in v , (r ◅ rs)

defaultFuel : Nat
defaultFuel = 64

nf₀ : Tm → Tm
nf₀ t = fst (nf defaultFuel t)

nfTy₀ : Ty → Ty
nfTy₀ A = fst (nfTy defaultFuel A)

------------------------------------------------------------------------
-- Certified equality.

infix 4 _==su_ _==suTy_
_==su_ : Tm → Tm → Bool
t ==su u = nf₀ t ==Tm nf₀ u

_==suTy_ : Ty → Ty → Bool
A ==suTy B = nfTy₀ A ==Ty nfTy₀ B

==su-sound : ∀ t u → T (t ==su u) → Σ Tm λ v → (t ⟶* v) × (u ⟶* v)
==su-sound t u p =
  nf₀ t , snd (nf defaultFuel t) ,
  subst (u ⟶*_) (sym (==Tm-sound (nf₀ t) (nf₀ u) p)) (snd (nf defaultFuel u))

==suTy-sound : ∀ A B → T (A ==suTy B) → Σ Ty λ C → (A ⟶ty* C) × (B ⟶ty* C)
==suTy-sound A B p =
  nfTy₀ A , snd (nfTy defaultFuel A) ,
  subst (B ⟶ty*_) (sym (==Ty-sound (nfTy₀ A) (nfTy₀ B) p)) (snd (nfTy defaultFuel B))
