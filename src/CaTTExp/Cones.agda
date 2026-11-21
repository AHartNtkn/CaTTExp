------------------------------------------------------------------------
-- Specified cone, cocone and conical-transfor contexts (ledger B5, B6).
--
-- Everything here is a *function* from a diagram context to a context,
-- not a judgment with many derivations: this is the repair asked for in
-- notes/limits-representables.md §4.1(1) and §10.3. The paper account,
-- with proofs, is notes/specified-cones.md.
--
-- What is checked, and how. Every context and substitution below is
-- run through the certified checker of CaTTExp.Check at typechecking
-- time (CaTTExp.ConesExamples): a `from-just` only typechecks if the
-- checker returns a derivation. The *general* statements (for every
-- globular Γ) are proved on paper; here they are machine-checked on a
-- suite of shapes. See notes/specified-cones.md §7 for the exact list.
--
-- Layer 1 (Cell): CaTT terms paired with their types, the binary
--   composite `binC k u w` of an n-cell and an m-cell along a k-cell,
--   identities, and iterated boundaries.
-- Layer 2 (Ex): a small expression language for the types of the
--   constructed contexts (variables, binary composites, identities),
--   with symbolic source/target, evaluated to CaTT syntax.
-- Layer 3: the constructions: cone, cocone, cylinder (hence ctrf),
--   suspension, constant diagram.
------------------------------------------------------------------------
module CaTTExp.Cones where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)

------------------------------------------------------------------------
-- Small list utilities

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

nth : ∀ {a} {A : Set a} → A → List A → Nat → A
nth d []       _       = d
nth d (x ∷ _)  zero    = x
nth d (_ ∷ xs) (suc n) = nth d xs n

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

range : Nat → List Nat          -- [0, …, n−1]
range n = go n []
  where
  go : Nat → List Nat → List Nat
  go zero    acc = acc
  go (suc k) acc = go k (k ∷ acc)

rangeFrom : Nat → Nat → List Nat   -- [a, …, a+n−1]
rangeFrom a n = map (λ i → a + i) (range n)

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p []       = false
any p (x ∷ xs) = p x ∨ any p xs

count : ∀ {a} {A : Set a} → (A → Bool) → List A → Nat
count p []       = 0
count p (x ∷ xs) = if p x then suc (count p xs) else count p xs

_≤ℕ_ : Nat → Nat → Bool
m ≤ℕ n = m <ℕ suc n

lookupTy : Ctx → Nat → Ty
lookupTy Γ i with lookup Γ i
... | just A  = A
... | nothing = ⋆

------------------------------------------------------------------------
-- Layer 1: cells (a term together with its type)

Cell : Set
Cell = Tm × Ty

dimC : Cell → Nat
dimC (_ , A) = dim A

-- Source and target of a positive-dimensional cell.
srcC tgtC : Cell → Cell
srcC (_ , arr A s _) = s , A
srcC (t , ⋆)         = t , ⋆
tgtC (_ , arr A _ u) = u , A
tgtC (t , ⋆)         = t , ⋆

-- The disk context Dⁿ and the substitution classifying an n-cell.
-- Dⁿ lists x, y, then the hom-disk: s^n u, t^n u, …, s u, t u, u.
nest : Nat → Tree
nest zero    = leaf
nest (suc n) = node (nest n ∷ [])

Disk : Nat → Ctx
Disk n = ctxOf (nest n)

diskList : Cell → List Tm
diskList c = go (dimC c) c
  where
  go : Nat → Cell → List Tm
  go zero    c = fst c ∷ []
  go (suc n) c = go n (srcC c) ++ (fst (tgtC c) ∷ fst c ∷ [])

-- The tail of diskList w after its first k-dimensional disk
-- (the part of w's disk not shared with what it is glued to).
restDisk : Nat → Cell → List Tm
restDisk k c = go (dimC c) c
  where
  go : Nat → Cell → List Tm
  go zero    c = []
  go (suc n) c = if dimC c ==ℕ k then []
                 else (go n (srcC c) ++ (fst (tgtC c) ∷ fst c ∷ []))

-- The pasting tree of a p-disk and a q-disk glued along a k-disk.
glueT : Nat → Nat → Nat → Tree
glueT zero    p q = node (nest (p ∸ 1) ∷ nest (q ∸ 1) ∷ [])
glueT (suc k) p q = node (glueT k (p ∸ 1) (q ∸ 1) ∷ [])

Glue : Nat → Nat → Nat → Ctx
Glue k p q = ctxOf (glueT k p q)

-- The generic cell at a level of a context.
gen : Ctx → Nat → Cell
gen Γ i = var i , lookupTy Γ i

-- Identity on a cell: the full coherence u → u over the disk of u.
idC : Cell → Cell
idC c = coh D (arr (lookupTy D (2 * n)) (var (2 * n)) (var (2 * n))) ⟪ diskList c ⟫
      , arr (snd c) (fst c) (fst c)
  where
  n = dimC c
  D = Disk n
  _*_ : Nat → Nat → Nat
  zero  * m = zero
  suc a * m = m + (a * m)

-- Binary composite u ∗_k w (k < dim u, k < dim w). Its type in the
-- glued pasting context is computed by the same function one dimension
-- down: the source of u ∗_k w is (∂⁻u) ∗_k (∂⁻w), where a factor of
-- dimension below the composite's is left unchanged; when both factors
-- have dimension k+1 the boundary is ∂⁻u → ∂⁺w. Fuel bounds the
-- recursion on dimension.
binF : Nat → Nat → Cell → Cell → Cell
binF zero       k u w = fst u , ⋆                     -- out of fuel: unreachable for the inputs used
binF (suc fuel) k u w = coh P A σ , A [ σ ]ty
  where
  p = dimC u
  q = dimC w
  r = max p q
  P = Glue k p q
  gu = gen P (p + p)
  gw = gen P (len P ∸ 1)
  lo hi : Cell → Cell
  lo c = if dimC c <ℕ r then c else srcC c
  hi c = if dimC c <ℕ r then c else tgtC c
  s' = binF fuel k (lo gu) (lo gw)
  t' = binF fuel k (hi gu) (hi gw)
  A : Ty
  A = if r ==ℕ suc k then arr (snd (srcC gu)) (fst (srcC gu)) (fst (tgtC gw))
      else arr (snd s') (fst s') (fst t')
  σ = ⟪ diskList u ++ restDisk k w ⟫

binC : Nat → Cell → Cell → Cell
binC k u w = binF (suc (max (dimC u) (dimC w))) k u w

-- Two named coherences on 2-cells, used by the depth-1 lifts of the
-- cylinder construction (ledger B18). Both are coherence-case cohs
-- (both sides full) over pasting contexts.
--
-- xchC u w, for 2-cells u : f ⇒ g : x → y and w : h ⇒ k : y → z, is the
-- interchange  (f ∗₀ w) ∗₁ (u ∗₀ k)  ⇛  (u ∗₀ h) ∗₁ (g ∗₀ w),
-- over D² ∨₀ D² (levels x0 y1 f2 g3 u4 z5 h6 k7 w8); with dir = false,
-- its reverse.
xchC : Bool → Cell → Cell → Cell
xchC dir u w = coh Q B σ , B [ σ ]ty
  where
  Q = Glue 0 2 2
  f = gen Q 2 ; g = gen Q 3 ; a = gen Q 4 ; h = gen Q 6 ; k = gen Q 7 ; b = gen Q 8
  s = binC 1 (binC 0 f b) (binC 0 a k)
  t = binC 1 (binC 0 a h) (binC 0 g b)
  B = if dir then arr (snd s) (fst s) (fst t) else arr (snd s) (fst t) (fst s)
  σ = ⟪ diskList u ++ restDisk 0 w ⟫

-- Unitors and associators on 1-cells, used by cones over 1-dimensional
-- coherence terms (ledger B19/B25): for a 1-cell w : x → y,
--   ruC w : w ⇒ w ∗₀ id_y,   luC w : w ⇒ id_x ∗₀ w   (full cohs over D¹),
-- and for composable 1-cells u, v, w,
--   assoc1C true u v w : (u ∗₀ v) ∗₀ w ⇒ u ∗₀ (v ∗₀ w)   (false: reverse).
ruC luC : Cell → Cell
ruC w = coh D B ⟪ diskList w ⟫ , B [ ⟪ diskList w ⟫ ]ty
  where
  D = Disk 1
  f = gen D 2
  B = arr (snd f) (fst f) (fst (binC 0 f (idC (gen D 1))))
luC w = coh D B ⟪ diskList w ⟫ , B [ ⟪ diskList w ⟫ ]ty
  where
  D = Disk 1
  f = gen D 2
  B = arr (snd f) (fst f) (fst (binC 0 (idC (gen D 0)) f))

assoc1C : Bool → Cell → Cell → Cell → Cell
assoc1C dir u v w = coh Q B σ , B [ σ ]ty
  where
  Q = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))
  a = gen Q 2 ; b = gen Q 4 ; c = gen Q 6
  l = binC 0 (binC 0 a b) c
  r = binC 0 a (binC 0 b c)
  B = if dir then arr (snd l) (fst l) (fst r) else arr (snd l) (fst r) (fst l)
  σ = ⟪ diskList u ++ restDisk 0 v ++ restDisk 0 w ⟫

-- Coherences used by cones over 2-dimensional coherence terms (ledger
-- B19): each is a coherence-case coh over the named pasting context.
private
  cohOver : Ctx → Cell → Cell → List Tm → Cell
  cohOver Q s t ts = coh Q B ⟪ ts ⟫ , B [ ⟪ ts ⟫ ]ty
    where B = arr (snd s) (fst s) (fst t)

-- dwC u a b : (u ∗₀ a) ∗₁ (u ∗₀ b) ⇛ u ∗₀ (a ∗₁ b)   (u a 1-cell; a, b vertical 2-cells)
dwC : Cell → Cell → Cell → Cell
dwC u a b = cohOver Q (binC 1 (binC 0 U A) (binC 0 U B)) (binC 0 U (binC 1 A B))
                    (diskList u ++ restDisk 0 a ++ restDisk 1 b)
  where
  Q = ctxOf (node (leaf ∷ node (leaf ∷ leaf ∷ []) ∷ []))
  U = gen Q 2 ; A = gen Q 6 ; B = gen Q 8

-- drC a b u : (a ∗₁ b) ∗₀ u ⇛ (a ∗₀ u) ∗₁ (b ∗₀ u)
drC : Cell → Cell → Cell → Cell
drC a b u = cohOver Q (binC 0 (binC 1 A B) U) (binC 1 (binC 0 A U) (binC 0 B U))
                    (diskList a ++ restDisk 1 b ++ restDisk 0 u)
  where
  Q = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ leaf ∷ []))
  A = gen Q 4 ; B = gen Q 6 ; U = gen Q 8

-- naC u a α : ((u ∗₀ a) ∗₀ α) ∗₁ a1(u, a, τα) ⇛ a1(u, a, σα) ∗₁ (u ∗₀ (a ∗₀ α))
naC : Cell → Cell → Cell → Cell
naC u a α = cohOver Q (binC 1 (binC 0 (binC 0 U A) Al) (assoc1C true U A G))
                      (binC 1 (assoc1C true U A F) (binC 0 U (binC 0 A Al)))
                    (diskList u ++ restDisk 0 a ++ restDisk 0 α)
  where
  Q = ctxOf (node (leaf ∷ leaf ∷ node (leaf ∷ []) ∷ []))
  U = gen Q 2 ; A = gen Q 4 ; F = gen Q 6 ; G = gen Q 7 ; Al = gen Q 8

-- nrC u α b : ((u ∗₀ α) ∗₀ b) ∗₁ a1(u, τα, b) ⇛ a1(u, σα, b) ∗₁ (u ∗₀ (α ∗₀ b))
nrC : Cell → Cell → Cell → Cell
nrC u α b = cohOver Q (binC 1 (binC 0 (binC 0 U Al) B) (assoc1C true U G B))
                      (binC 1 (assoc1C true U F B) (binC 0 U (binC 0 Al B)))
                    (diskList u ++ restDisk 0 α ++ restDisk 0 b)
  where
  Q = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ leaf ∷ []))
  U = gen Q 2 ; F = gen Q 4 ; G = gen Q 5 ; Al = gen Q 6 ; B = gen Q 8

-- ru2C a : a ⇛ a ∗₁ id_{τa}   (a a 2-cell)
ru2C : Cell → Cell
ru2C a = cohOver Q A (binC 1 A (idC (gen Q 3))) (diskList a)
  where
  Q = Disk 2
  A = gen Q 4

-- wiC u f : id_{u ∗₀ f} ⇛ u ∗₀ id_f
wiC : Cell → Cell → Cell
wiC u f = cohOver Q (idC (binC 0 U F)) (binC 0 U (idC F)) (diskList u ++ restDisk 0 f)
  where
  Q = ctxOf (node (leaf ∷ leaf ∷ []))
  U = gen Q 2 ; F = gen Q 4

-- hxC a b : (a ∗₀ σb) ∗₁ (τa ∗₀ b) ⇛ a ∗₀ b   (horizontal composite as whiskers)
hxC : Cell → Cell → Cell
hxC a b = cohOver Q (binC 1 (binC 0 A (gen Q 6)) (binC 0 (gen Q 3) B)) (binC 0 A B)
                  (diskList a ++ restDisk 0 b)
  where
  Q = Glue 0 2 2
  A = gen Q 4 ; B = gen Q 8

-- O_odd duals of the cells above, used by cocones over 2-dimensional
-- coherence terms. Under O_odd, ∗₀ factors swap, 2-cells keep their
-- direction and 3-cells reverse.

-- ru2rC a : a ∗₁ id_{τa} ⇛ a   (dual of ru2C)
ru2rC : Cell → Cell
ru2rC a = cohOver Q (binC 1 A (idC (gen Q 3))) A (diskList a)
  where
  Q = Disk 2
  A = gen Q 4

-- wirC f u : id_f ∗₀ u ⇛ id_{f ∗₀ u}   (dual of wiC)
wirC : Cell → Cell → Cell
wirC f u = cohOver Q (binC 0 (idC F) U) (idC (binC 0 F U)) (diskList f ++ restDisk 0 u)
  where
  Q = ctxOf (node (leaf ∷ leaf ∷ []))
  F = gen Q 2 ; U = gen Q 4

-- naDC α a u : a1R(σα, a, u) ∗₁ ((α ∗₀ a) ∗₀ u) ⇛ (α ∗₀ (a ∗₀ u)) ∗₁ a1R(τα, a, u)
naDC : Cell → Cell → Cell → Cell
naDC α a u = cohOver Q (binC 1 (assoc1C false F A U) (binC 0 (binC 0 Al A) U))
                       (binC 1 (binC 0 Al (binC 0 A U)) (assoc1C false G A U))
                     (diskList α ++ restDisk 0 a ++ restDisk 0 u)
  where
  Q = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ leaf ∷ []))
  F = gen Q 2 ; G = gen Q 3 ; Al = gen Q 4 ; A = gen Q 6 ; U = gen Q 8

-- nrDC b α u : a1R(b, σα, u) ∗₁ ((b ∗₀ α) ∗₀ u) ⇛ (b ∗₀ (α ∗₀ u)) ∗₁ a1R(b, τα, u)
nrDC : Cell → Cell → Cell → Cell
nrDC b α u = cohOver Q (binC 1 (assoc1C false B F U) (binC 0 (binC 0 B Al) U))
                       (binC 1 (binC 0 B (binC 0 Al U)) (assoc1C false B G U))
                     (diskList b ++ restDisk 0 α ++ restDisk 0 u)
  where
  Q = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ leaf ∷ []))
  B = gen Q 2 ; F = gen Q 4 ; G = gen Q 5 ; Al = gen Q 6 ; U = gen Q 8

-- hxDC b a : b ∗₀ a ⇛ (σb ∗₀ a) ∗₁ (b ∗₀ τa)   (dual of hxC)
hxDC : Cell → Cell → Cell
hxDC b a = cohOver Q (binC 0 B A) (binC 1 (binC 0 (gen Q 2) A) (binC 0 B (gen Q 7)))
                   (diskList b ++ restDisk 0 a)
  where
  Q = Glue 0 2 2
  B = gen Q 4 ; A = gen Q 8

-- assocC dir u v w, for 2-cells composable along 1-cells, is the
-- associator (u ∗₁ v) ∗₁ w ⇛ u ∗₁ (v ∗₁ w) (dir = true) or its reverse
-- (dir = false), over three 2-disks glued along 1-disks.
assocC : Bool → Cell → Cell → Cell → Cell
assocC dir u v w = coh Q B σ , B [ σ ]ty
  where
  Q = ctxOf (node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ []))
  a = gen Q 4 ; b = gen Q 6 ; c = gen Q 8
  l = binC 1 (binC 1 a b) c
  r = binC 1 a (binC 1 b c)
  B = if dir then arr (snd l) (fst l) (fst r) else arr (snd l) (fst r) (fst l)
  σ = ⟪ diskList u ++ restDisk 1 v ++ restDisk 1 w ⟫

------------------------------------------------------------------------
-- Layer 2: expressions for context types

data Ex : Set where
  v   : Nat → Ex              -- a variable (de Bruijn level)
  bn  : Nat → Ex → Ex → Ex    -- binary composite along a k-cell
  idn : Ex → Ex               -- identity
  xc  : Ex → Ex → Ex          -- interchange of two 2-cells (xchC)
  xr  : Ex → Ex → Ex          -- its reverse
  asL asR : Ex → Ex → Ex → Ex -- associator of three 2-cells along 1-cells, and its reverse
  ru lu : Ex → Ex             -- unitors on a 1-cell: w ⇒ w ∗₀ id, w ⇒ id ∗₀ w
  a1L a1R : Ex → Ex → Ex → Ex -- associator of three 1-cells, and its reverse
  dw dr na nr : Ex → Ex → Ex → Ex  -- the 3-cells dwC, drC, naC, nrC
  ru2 : Ex → Ex                    -- ru2C
  wi hx : Ex → Ex → Ex             -- wiC, hxC
  naD nrD : Ex → Ex → Ex → Ex      -- their O_odd duals: naDC, nrDC,
  ru2r : Ex → Ex                   -- ru2rC,
  wir hxD : Ex → Ex → Ex           -- wirC, hxDC

data ExTy : Set where
  ob  : ExTy
  hom : ExTy → Ex → Ex → ExTy

ExCtx : Set
ExCtx = List ExTy

dimE : ExTy → Nat
dimE ob          = 0
dimE (hom A _ _) = suc (dimE A)

srcE tgtE : ExTy → Ex
srcE (hom _ s _) = s
srcE ob          = v 0
tgtE (hom _ _ t) = t
tgtE ob          = v 0

baseE : ExTy → ExTy
baseE (hom A _ _) = A
baseE ob          = ob

-- Symbolic type of an expression in an ExCtx.
tyF : Nat → ExCtx → Ex → ExTy
tyF zero       Γ e = ob
tyF (suc f) Γ (v i)      = nth ob Γ i
tyF (suc f) Γ (idn e)    = hom (tyF f Γ e) e e
tyF (suc f) Γ (xc u w)   = hom (tyF f Γ s) s t
  where
  A = tyF f Γ u
  B = tyF f Γ w
  s = bn 1 (bn 0 (srcE A) w) (bn 0 u (tgtE B))
  t = bn 1 (bn 0 u (srcE B)) (bn 0 (tgtE A) w)
tyF (suc f) Γ (xr u w)   = hom (tyF f Γ s) t s
  where
  A = tyF f Γ u
  B = tyF f Γ w
  s = bn 1 (bn 0 (srcE A) w) (bn 0 u (tgtE B))
  t = bn 1 (bn 0 u (srcE B)) (bn 0 (tgtE A) w)
tyF (suc f) Γ (ru w)     = hom (tyF f Γ w) w (bn 0 w (idn (tgtE (tyF f Γ w))))
tyF (suc f) Γ (lu w)     = hom (tyF f Γ w) w (bn 0 (idn (srcE (tyF f Γ w))) w)
tyF (suc f) Γ (dw u a b) = hom (tyF f Γ s) s (bn 0 u (bn 1 a b))
  where s = bn 1 (bn 0 u a) (bn 0 u b)
tyF (suc f) Γ (dr a b u) = hom (tyF f Γ s) s (bn 1 (bn 0 a u) (bn 0 b u))
  where s = bn 0 (bn 1 a b) u
tyF (suc f) Γ (na u a w) = hom (tyF f Γ s) s (bn 1 (a1L u a (srcE W)) (bn 0 u (bn 0 a w)))
  where
  W = tyF f Γ w
  s = bn 1 (bn 0 (bn 0 u a) w) (a1L u a (tgtE W))
tyF (suc f) Γ (nr u w b) = hom (tyF f Γ s) s (bn 1 (a1L u (srcE W) b) (bn 0 u (bn 0 w b)))
  where
  W = tyF f Γ w
  s = bn 1 (bn 0 (bn 0 u w) b) (a1L u (tgtE W) b)
tyF (suc f) Γ (ru2 a)    = hom (tyF f Γ a) a (bn 1 a (idn (tgtE (tyF f Γ a))))
tyF (suc f) Γ (wi u w)   = hom (tyF f Γ s) s (bn 0 u (idn w))
  where s = idn (bn 0 u w)
tyF (suc f) Γ (hx a b)   = hom (tyF f Γ s) s (bn 0 a b)
  where s = bn 1 (bn 0 a (srcE (tyF f Γ b))) (bn 0 (tgtE (tyF f Γ a)) b)
tyF (suc f) Γ (ru2r a)   = hom (tyF f Γ s) s a
  where s = bn 1 a (idn (tgtE (tyF f Γ a)))
tyF (suc f) Γ (wir w u)  = hom (tyF f Γ s) s (idn (bn 0 w u))
  where s = bn 0 (idn w) u
tyF (suc f) Γ (naD w a u) = hom (tyF f Γ s) s (bn 1 (bn 0 w (bn 0 a u)) (a1R (tgtE W) a u))
  where
  W = tyF f Γ w
  s = bn 1 (a1R (srcE W) a u) (bn 0 (bn 0 w a) u)
tyF (suc f) Γ (nrD b w u) = hom (tyF f Γ s) s (bn 1 (bn 0 b (bn 0 w u)) (a1R b (tgtE W) u))
  where
  W = tyF f Γ w
  s = bn 1 (a1R b (srcE W) u) (bn 0 (bn 0 b w) u)
tyF (suc f) Γ (hxD b a)  = hom (tyF f Γ s) s (bn 1 (bn 0 (srcE (tyF f Γ b)) a) (bn 0 b (tgtE (tyF f Γ a))))
  where s = bn 0 b a
tyF (suc f) Γ (a1L u y w) = hom (tyF f Γ l) l (bn 0 u (bn 0 y w))
  where l = bn 0 (bn 0 u y) w
tyF (suc f) Γ (a1R u y w) = hom (tyF f Γ l) (bn 0 u (bn 0 y w)) l
  where l = bn 0 (bn 0 u y) w
tyF (suc f) Γ (asL u y w) = hom (tyF f Γ l) l (bn 1 u (bn 1 y w))
  where l = bn 1 (bn 1 u y) w
tyF (suc f) Γ (asR u y w) = hom (tyF f Γ l) (bn 1 u (bn 1 y w)) l
  where l = bn 1 (bn 1 u y) w
tyF (suc f) Γ (bn k u w) =
  if r ==ℕ suc k then hom (baseE A) (srcE A) (tgtE B)
  else hom (tyF f Γ s') s' t'
  where
  A = tyF f Γ u
  B = tyF f Γ w
  r = max (dimE A) (dimE B)
  lo hi : ExTy → Ex → Ex
  lo C e = if dimE C <ℕ r then e else srcE C
  hi C e = if dimE C <ℕ r then e else tgtE C
  s' = bn k (lo A u) (lo B w)
  t' = bn k (hi A u) (hi B w)

fuel : Nat
fuel = 64

tyE : ExCtx → Ex → ExTy
tyE = tyF fuel

-- Evaluation to CaTT syntax.
mutual
  evF : Nat → ExCtx → Ex → Tm
  evF zero    Γ e          = var 0
  evF (suc f) Γ (v i)      = var i
  evF (suc f) Γ (idn e)    = fst (idC (cellF f Γ e))
  evF (suc f) Γ (bn k u w) = fst (binC k (cellF f Γ u) (cellF f Γ w))
  evF (suc f) Γ (xc u w)   = fst (xchC true  (cellF f Γ u) (cellF f Γ w))
  evF (suc f) Γ (xr u w)   = fst (xchC false (cellF f Γ u) (cellF f Γ w))
  evF (suc f) Γ (ru w)     = fst (ruC (cellF f Γ w))
  evF (suc f) Γ (lu w)     = fst (luC (cellF f Γ w))
  evF (suc f) Γ (dw u a b) = fst (dwC (cellF f Γ u) (cellF f Γ a) (cellF f Γ b))
  evF (suc f) Γ (dr a b u) = fst (drC (cellF f Γ a) (cellF f Γ b) (cellF f Γ u))
  evF (suc f) Γ (na u a w) = fst (naC (cellF f Γ u) (cellF f Γ a) (cellF f Γ w))
  evF (suc f) Γ (nr u w b) = fst (nrC (cellF f Γ u) (cellF f Γ w) (cellF f Γ b))
  evF (suc f) Γ (ru2 a)    = fst (ru2C (cellF f Γ a))
  evF (suc f) Γ (wi u w)   = fst (wiC (cellF f Γ u) (cellF f Γ w))
  evF (suc f) Γ (hx a b)   = fst (hxC (cellF f Γ a) (cellF f Γ b))
  evF (suc f) Γ (ru2r a)   = fst (ru2rC (cellF f Γ a))
  evF (suc f) Γ (wir w u)  = fst (wirC (cellF f Γ w) (cellF f Γ u))
  evF (suc f) Γ (naD w a u) = fst (naDC (cellF f Γ w) (cellF f Γ a) (cellF f Γ u))
  evF (suc f) Γ (nrD b w u) = fst (nrDC (cellF f Γ b) (cellF f Γ w) (cellF f Γ u))
  evF (suc f) Γ (hxD b a)  = fst (hxDC (cellF f Γ b) (cellF f Γ a))
  evF (suc f) Γ (a1L u y w) = fst (assoc1C true  (cellF f Γ u) (cellF f Γ y) (cellF f Γ w))
  evF (suc f) Γ (a1R u y w) = fst (assoc1C false (cellF f Γ u) (cellF f Γ y) (cellF f Γ w))
  evF (suc f) Γ (asL u y w) = fst (assocC true  (cellF f Γ u) (cellF f Γ y) (cellF f Γ w))
  evF (suc f) Γ (asR u y w) = fst (assocC false (cellF f Γ u) (cellF f Γ y) (cellF f Γ w))

  evTyF : Nat → ExCtx → ExTy → Ty
  evTyF zero    Γ A           = ⋆
  evTyF (suc f) Γ ob          = ⋆
  evTyF (suc f) Γ (hom A s t) = arr (evTyF f Γ A) (evF f Γ s) (evF f Γ t)

  cellF : Nat → ExCtx → Ex → Cell
  cellF zero    Γ e = var 0 , ⋆
  cellF (suc f) Γ e = evF f Γ e , evTyF f Γ (tyE Γ e)

ev : ExCtx → Ex → Tm
ev = evF fuel

evTy : ExCtx → ExTy → Ty
evTy = evTyF fuel

cellE : ExCtx → Ex → Cell
cellE = cellF fuel

-- An ExCtx as a CaTT context.
evCtx : ExCtx → Ctx
evCtx Γ = go Γ ε
  where
  go : ExCtx → Ctx → Ctx
  go []       acc = acc
  go (A ∷ As) acc = go As (acc ▸ evTy Γ A)

-- Renaming and substitution of expressions.
substE : (Nat → Ex) → Ex → Ex
substE ρ (v i)      = ρ i
substE ρ (bn k u w) = bn k (substE ρ u) (substE ρ w)
substE ρ (idn e)    = idn (substE ρ e)
substE ρ (xc u w)   = xc (substE ρ u) (substE ρ w)
substE ρ (xr u w)   = xr (substE ρ u) (substE ρ w)
substE ρ (ru w)     = ru (substE ρ w)
substE ρ (lu w)     = lu (substE ρ w)
substE ρ (dw u a b) = dw (substE ρ u) (substE ρ a) (substE ρ b)
substE ρ (dr a b u) = dr (substE ρ a) (substE ρ b) (substE ρ u)
substE ρ (na u a w) = na (substE ρ u) (substE ρ a) (substE ρ w)
substE ρ (nr u w b) = nr (substE ρ u) (substE ρ w) (substE ρ b)
substE ρ (ru2 a)    = ru2 (substE ρ a)
substE ρ (wi u w)   = wi (substE ρ u) (substE ρ w)
substE ρ (hx a b)   = hx (substE ρ a) (substE ρ b)
substE ρ (ru2r a)   = ru2r (substE ρ a)
substE ρ (wir w u)  = wir (substE ρ w) (substE ρ u)
substE ρ (naD w a u) = naD (substE ρ w) (substE ρ a) (substE ρ u)
substE ρ (nrD b w u) = nrD (substE ρ b) (substE ρ w) (substE ρ u)
substE ρ (hxD b a)  = hxD (substE ρ b) (substE ρ a)
substE ρ (a1L u y w) = a1L (substE ρ u) (substE ρ y) (substE ρ w)
substE ρ (a1R u y w) = a1R (substE ρ u) (substE ρ y) (substE ρ w)
substE ρ (asL u y w) = asL (substE ρ u) (substE ρ y) (substE ρ w)
substE ρ (asR u y w) = asR (substE ρ u) (substE ρ y) (substE ρ w)

substTyE : (Nat → Ex) → ExTy → ExTy
substTyE ρ ob          = ob
substTyE ρ (hom A s t) = hom (substTyE ρ A) (substE ρ s) (substE ρ t)

varsE : Ex → List Nat
varsE (v i)      = i ∷ []
varsE (bn _ u w) = varsE u ++ varsE w
varsE (idn e)    = varsE e
varsE (xc u w)   = varsE u ++ varsE w
varsE (xr u w)   = varsE u ++ varsE w
varsE (ru w)     = varsE w
varsE (lu w)     = varsE w
varsE (dw u a b) = varsE u ++ varsE a ++ varsE b
varsE (dr a b u) = varsE a ++ varsE b ++ varsE u
varsE (na u a w) = varsE u ++ varsE a ++ varsE w
varsE (nr u w b) = varsE u ++ varsE w ++ varsE b
varsE (ru2 a)    = varsE a
varsE (wi u w)   = varsE u ++ varsE w
varsE (hx a b)   = varsE a ++ varsE b
varsE (ru2r a)   = varsE a
varsE (wir w u)  = varsE w ++ varsE u
varsE (naD w a u) = varsE w ++ varsE a ++ varsE u
varsE (nrD b w u) = varsE b ++ varsE w ++ varsE u
varsE (hxD b a)  = varsE b ++ varsE a
varsE (a1L u y w) = varsE u ++ varsE y ++ varsE w
varsE (a1R u y w) = varsE u ++ varsE y ++ varsE w
varsE (asL u y w) = varsE u ++ varsE y ++ varsE w
varsE (asR u y w) = varsE u ++ varsE y ++ varsE w

idxE : Ex → Nat
idxE (v i) = i
idxE _     = 0

-- Iterated source and target, as expressions.
srcIter tgtIter : ExCtx → Nat → Ex → Ex
srcIter Γ zero    e = e
srcIter Γ (suc k) e = srcIter Γ k (srcE (tyE Γ e))
tgtIter Γ zero    e = e
tgtIter Γ (suc k) e = tgtIter Γ k (tgtE (tyE Γ e))

-- A context is globular when every boundary of every variable is a
-- variable (Mikhail's Thm 3.3 setting; includes all pasting contexts
-- and contexts with loops and parallel cells).
isVar : Ex → Bool
isVar (v _) = true
isVar _     = false

globularTy : ExTy → Bool
globularTy ob          = true
globularTy (hom A s t) = isVar s ∧ isVar t ∧ globularTy A

globular : ExCtx → Bool
globular Γ = all globularTy Γ

------------------------------------------------------------------------
-- Layer 3a: the specified cone (Mikhail, Thm 3.3; lax at the vertices)
--
-- Context layout: Γ (levels 0 … n−1), apex c (level n), then one
-- projection p_x (level n+1+x) for each variable x of Γ, in order.
--
--   p_x : c → x                                              (dim x = 0)
--   p_t : p_{τt} → p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} (… (p_{σᵐt} ∗₀ t)))
--                                                             (dim t = m ≥ 1)

module ConeOf (Γ : ExCtx) where
  n = length Γ
  c = v n
  pr : Nat → Ex
  pr i = v (suc (n + i))

  -- p applied to a variable expression of Γ.
  pE : Ex → Ex
  pE e = pr (idxE e)

  -- The long side T_t, built from the inside out.
  longSide : Nat → ExTy → Ex
  longSide x A = go 1 (bn 0 (pE (srcIter Γ m (v x))) (v x))
    where
    m = dimE A
    go : Nat → Ex → Ex
    go j acc = if m ≤ℕ j then acc
               else goF m j acc
      where
      goF : Nat → Nat → Ex → Ex
      goF zero    j acc = acc
      goF (suc f) j acc =
        if m ≤ℕ j then acc
        else goF f (suc j) (bn j (pE (srcIter Γ (m ∸ j) (v x))) acc)

  projTy : ExCtx → Nat → ExTy → ExTy
  projTy K x ob          = hom ob c (v x)
  projTy K x (hom A s t) = hom (tyE K (pE t)) (pE t) (longSide x (hom A s t))

  build : Nat → ExCtx → ExCtx → ExCtx
  build x K []       = K
  build x K (A ∷ As) = build (suc x) (K ++ (projTy K x A ∷ [])) As

  cone : ExCtx
  cone = build 0 (Γ ++ (ob ∷ [])) Γ

  projLevels : List Nat
  projLevels = rangeFrom (suc n) n

------------------------------------------------------------------------
-- Layer 3b: the specified cocone, the dual of the cone in the odd
-- dimensions (so that its constant-diagram instance has no opposites):
--
--   q_x : x → c                                                (dim 0)
--   q_t : q_{σt} → E_t        (dim t odd)
--   q_t : E_t → q_{τt}        (dim t even, ≥ 2)
--
-- with E_t = X_{m−1}, X_0 = t ∗₀ q_{u_m},
--      X_j = X_{j−1} ∗_j q_{u_{m−j}} (j even), q_{u_{m−j}} ∗_j X_{j−1} (j odd),
-- where u_0 = t and u_{k+1} is the source of u_k if dim u_k is even and
-- its target if dim u_k is odd.

------------------------------------------------------------------------
-- Cones over contexts whose boundaries are 1-dimensional coherence
-- terms (ledger B19, B25; notes/specified-cones.md §5): the cone cell
-- over a term is defined by recursion,
--   P(x)          = p_x
--   P(id_x)       = ru(p_x)                     : p_x ⇒ p_x ∗₀ id_x
--   P(a ∗₀ b)     = (P b ∗₁ (P a ∗₀ b)) ∗₁ a1L(p_X, a, b)
--                                               : p_Z ⇒ p_X ∗₀ (a ∗₀ b)
-- for 1-dimensional a : X → M, b : M → Z. Any other term (identities of
-- 1-cells, 2-dimensional composites, …) gives nothing: those need N^cone
-- in dimension ≥ 2 and are not implemented. On globular Γ this is
-- ConeOf.cone (checked by refl in ConesExamples).

module ConeT (Γ : ExCtx) where
  private
    n = length Γ
    c = v n
    pr : Nat → Ex
    pr i = v (suc (n + i))
    dimΓ : Ex → Nat
    dimΓ e = dimE (tyE Γ e)
    pObj : Ex → Maybe Ex
    pObj (v i) = just (pr i)
    pObj _     = nothing

  srcΓ tgtΓ : Ex → Ex
  srcΓ e = srcE (tyE Γ e)
  tgtΓ e = tgtE (tyE Γ e)

  -- P on terms of dimension ≤ 2, by recursion (with fuel, since the
  -- horizontal case recurses on a rewritten term).
  PF : Nat → Ex → Maybe Ex
  PF zero _ = nothing
  PF (suc fl) (v i) = just (pr i)
  PF (suc fl) (idn e) =
    if dimΓ e ==ℕ 0 then (pObj e >>= λ pe → just (ru pe))
    else if dimΓ e ==ℕ 1 then
      -- P(1_f) = ru2(P f) ∗₂ (P f ∗₁ wi(p_X, f))
      (PF fl e >>= λ Pe → pObj (srcΓ e) >>= λ pX →
       just (bn 2 (ru2 Pe) (bn 1 Pe (wi pX e))))
    else nothing
  PF (suc fl) (bn k a b) =
    if (k ==ℕ 0) ∧ (da ==ℕ 1) ∧ (db ==ℕ 1) then
      (PF fl a >>= λ Pa → PF fl b >>= λ Pb → pObj (srcΓ a) >>= λ pX →
       just (bn 1 (bn 1 Pb (bn 0 Pa b)) (a1L pX a b)))
    else if (k ==ℕ 1) ∧ (da ==ℕ 2) ∧ (db ==ℕ 2) then vert
    else if (k ==ℕ 0) ∧ (da ==ℕ 1) ∧ (db ==ℕ 2) then whiskL
    else if (k ==ℕ 0) ∧ (da ==ℕ 2) ∧ (db ==ℕ 1) then whiskR
    else if (k ==ℕ 0) ∧ (da ==ℕ 2) ∧ (db ==ℕ 2) then horiz
    else nothing
    where
    da = dimΓ a
    db = dimΓ b
    -- a ∗₁ b, with a : f ⇒ g, b : g ⇒ h over X → Y:
    --   P b ∗₂ (P a ∗₁ (p_X ∗₀ b)) ∗₂ asL(P f, p_X ∗₀ a, p_X ∗₀ b) ∗₂ (P f ∗₁ dw(p_X, a, b))
    vert : Maybe Ex
    vert = PF fl a >>= λ Pa → PF fl b >>= λ Pb → PF fl (srcΓ a) >>= λ Pf →
           pObj (srcΓ (srcΓ a)) >>= λ pX →
           just (bn 2 Pb (bn 2 (bn 1 Pa (bn 0 pX b))
                (bn 2 (asL Pf (bn 0 pX a) (bn 0 pX b)) (bn 1 Pf (dw pX a b)))))
    -- a ∗₀ α, with a : X → Y and α : f ⇒ g over Y → Z.
    whiskL : Maybe Ex
    whiskL = PF fl a >>= λ Pa → PF fl b >>= λ Pα → PF fl f >>= λ Pf →
             pObj (srcΓ a) >>= λ pX → pObj (tgtΓ a) >>= λ pY →
             let W  = bn 0 pY b
                 V  = bn 0 (bn 0 pX a) b
                 Ag = a1L pX a g
                 Af = a1L pX a f
                 L  = bn 1 Pf (bn 0 Pa f)
             in just (bn 2 (bn 1 (bn 1 Pα (bn 0 Pa g)) Ag)
                     (bn 2 (bn 1 (asL Pf W (bn 0 Pa g)) Ag)
                     (bn 2 (bn 1 (bn 1 Pf (xc Pa b)) Ag)
                     (bn 2 (bn 1 (asR Pf (bn 0 Pa f) V) Ag)
                     (bn 2 (asL L V Ag)
                     (bn 2 (bn 1 L (na pX a b))
                           (asR L Af (bn 0 pX (bn 0 a b)))))))))
      where
      f = srcΓ b
      g = tgtΓ b
    -- α ∗₀ b, with α : f ⇒ g over X → Y and b : Y → Z.
    whiskR : Maybe Ex
    whiskR = PF fl b >>= λ Pb → PF fl a >>= λ Pα → PF fl f >>= λ Pf →
             pObj (srcΓ f) >>= λ pX →
             let U   = bn 0 (bn 0 pX a) b
                 Ag  = a1L pX g b
                 Af  = a1L pX f b
                 L   = bn 1 Pb (bn 0 Pf b)
             in just (bn 2 (bn 1 (bn 1 Pb (bn 0 Pα b)) Ag)
                     (bn 2 (bn 1 (bn 1 Pb (dr Pf (bn 0 pX a) b)) Ag)
                     (bn 2 (bn 1 (asR Pb (bn 0 Pf b) U) Ag)
                     (bn 2 (asL L U Ag)
                     (bn 2 (bn 1 L (nr pX a b))
                           (asR L Af (bn 0 pX (bn 0 a b))))))))
      where
      f = srcΓ a
      g = tgtΓ a
    -- α ∗₀ β: transport the cone cell of (α ∗₀ σβ) ∗₁ (τα ∗₀ β) along hx.
    horiz : Maybe Ex
    horiz = PF fl vt >>= λ Pv → PF fl (srcΓ (bn 0 a b)) >>= λ Ps →
            pObj (srcΓ (srcΓ a)) >>= λ pX →
            just (bn 2 Pv (bn 1 Ps (bn 0 pX (hx a b))))
      where vt = bn 1 (bn 0 a (srcΓ b)) (bn 0 (tgtΓ a) b)
  PF (suc fl) _ = nothing

  P : Ex → Maybe Ex
  P = PF fuel

  longSide : Nat → ExTy → Maybe Ex
  longSide x A = P (srcIter Γ m (v x)) >>= λ p0 → go m 1 (bn 0 p0 (v x))
    where
    m = dimE A
    go : Nat → Nat → Ex → Maybe Ex
    go zero    j acc = just acc
    go (suc f) j acc =
      if m ≤ℕ j then just acc
      else (P (srcIter Γ (m ∸ j) (v x)) >>= λ pj → go f (suc j) (bn j pj acc))

  projTy : ExCtx → Nat → ExTy → Maybe ExTy
  projTy K x ob          = just (hom ob c (v x))
  projTy K x (hom A s t) = P t >>= λ pt → longSide x (hom A s t) >>= λ l →
                           just (hom (tyE K pt) pt l)

  build : Nat → ExCtx → ExCtx → Maybe ExCtx
  build x K []       = just K
  build x K (A ∷ As) = projTy K x A >>= λ B → build (suc x) (K ++ (B ∷ [])) As

  cone : Maybe ExCtx
  cone = build 0 (Γ ++ (ob ∷ [])) Γ

module CoconeOf (Γ : ExCtx) where
  n = length Γ
  c = v n
  qr : Nat → Ex
  qr i = v (suc (n + i))
  qE : Ex → Ex
  qE e = qr (idxE e)

  even : Nat → Bool
  even zero          = true
  even (suc zero)    = false
  even (suc (suc k)) = even k

  -- u_k for the cell x of dimension m.
  uSeq : Nat → Nat → Ex → Ex
  uSeq m zero    e = e
  uSeq m (suc k) e =
    let e' = uSeq m k e
        d  = m ∸ k
    in if even d then srcE (tyE Γ e') else tgtE (tyE Γ e')

  longSide : Nat → Nat → Ex
  longSide x m = goF m 1 (bn 0 (v x) (qE (uSeq m m (v x))))
    where
    goF : Nat → Nat → Ex → Ex
    goF zero    j acc = acc
    goF (suc f) j acc =
      if m ≤ℕ j then acc
      else goF f (suc j)
             (if even j then bn j acc (qE (uSeq m (m ∸ j) (v x)))
              else bn j (qE (uSeq m (m ∸ j) (v x))) acc)

  coprojTy : ExCtx → Nat → ExTy → ExTy
  coprojTy K x ob          = hom ob (v x) c
  coprojTy K x (hom A s t) =
    if even m then hom (tyE K (qE t)) (longSide x m) (qE t)
    else hom (tyE K (qE s)) (qE s) (longSide x m)
    where m = dimE (hom A s t)

  build : Nat → ExCtx → ExCtx → ExCtx
  build x K []       = K
  build x K (A ∷ As) = build (suc x) (K ++ (coprojTy K x A ∷ [])) As

  cocone : ExCtx
  cocone = build 0 (Γ ++ (ob ∷ [])) Γ

------------------------------------------------------------------------
-- Layer 3c: suspension and the constant diagram

-- Σ_{⊤,c} Γ: levels 0 (⊤) and 1 (c), then Γ shifted by 2.
suspTy : ExTy → ExTy
suspTy ob          = hom ob (v 0) (v 1)
suspTy (hom A s t) = hom (suspTy A) (substE (λ i → v (2 + i)) s) (substE (λ i → v (2 + i)) t)

susp : ExCtx → ExCtx
susp Γ = ob ∷ ob ∷ map suspTy Γ

-- The iterated identity on ⊤ (level 0) of dimension d.
idIter : Nat → Ex
idIter zero    = v 0
idIter (suc d) = idn (idIter d)

-- The constant-diagram instance of the cocone over a globular Γ:
-- context (⊤, c, q_x …) with x ↦ ⊤, t ↦ id^{dim t}_⊤.
constCocone : ExCtx → ExCtx
constCocone Γ = ob ∷ ob ∷ map (substTyE ρ) (dropN (suc n) (CoconeOf.cocone Γ))
  where
  n = length Γ
  dropN : Nat → ExCtx → ExCtx
  dropN zero    xs       = xs
  dropN (suc k) []       = []
  dropN (suc k) (_ ∷ xs) = dropN k xs
  ρ : Nat → Ex
  ρ i = if i <ℕ n then idIter (dimE (nth ob Γ i))
        else if i ==ℕ n then v 1
        else v (2 + (i ∸ suc n))

------------------------------------------------------------------------
-- Layer 3d: the cylinder Γ↑Y (the Gray cylinder I ⊗ Γ relative to an
-- up-closed set Y), with Lemma 1's types
--
--   a_x = ( … ((x⁻ ∗₀ (τⁿx)↑) ∗₁ (τⁿ⁻¹x)↑) … ) ∗_{n−1} (τx)↑
--   b_x = (σx)↑ ∗_{n−1} ( … ((σⁿ⁻¹x)↑ ∗₁ ((σⁿx)↑ ∗₀ x⁺)) … )
--
-- (unaffected factors omitted). Lifts of composite boundaries are
-- computed by the depth-0 rule (u ∗_k w)↑ = u↑ ∗_k w↑ (an unaffected
-- factor is kept); this rule is only claimed where Y has depth 0 in the
-- composite (notes/specified-cones.md §4), and the checker rejects any
-- other use. Identities of affected cells are not lifted (`nothing`).
--
-- Layout: walk Γ in order; x ∉ Y is kept, x ∈ Y becomes x⁻, x⁺, x↑.

record Cyl : Set where
  constructor mkCyl
  field
    ctx    : ExCtx
    minus  : Nat → Nat     -- level of x⁻ (or of x, if x ∉ Y)
    plus   : Nat → Nat     -- level of x⁺ (or of x)
    up     : Nat → Nat     -- level of x↑ (meaningless if x ∉ Y)
    upLvls : List Nat      -- the levels of the x↑, in order

module CylOf (Γ : ExCtx) (Y : List Nat) where
  inY : Nat → Bool
  inY i = elem i Y

  affected : Ex → Bool
  affected e = any inY (varsE e)

  -- Positions, computed by a prefix walk.
  pos : Nat → Nat        -- level of the first new variable for x
  pos zero    = 0
  pos (suc x) = pos x + (if inY x then 3 else 1)

  mi pl upl : Nat → Nat
  mi x = pos x
  pl x = if inY x then suc (pos x) else pos x
  upl x = suc (suc (pos x))

  ren⁻ ren⁺ : Ex → Ex
  ren⁻ = substE (λ i → v (mi i))
  ren⁺ = substE (λ i → v (pl i))

  dimΓ : Ex → Nat
  dimΓ e = dimE (tyE Γ e)

  -- lift t : a_t → b_t, the naturality cell of an affected term t.
  -- Rules (notes/specified-cones.md §4.3):
  -- * depth 0: an affected factor of the composite's own dimension,
  --   whiskered by unaffected cells, lifts factorwise;
  -- * depth 1, whisker: u ∗₀ w with u an affected 1-cell and w an
  --   unaffected 2-cell lifts to the interchange xc u↑ w; mirrored, an
  --   unaffected 2-cell u and an affected 1-cell w give xr u w↑;
  -- * depth 1, paste: u ∗₁ w with u, w affected 2-cells (and affected
  --   1-dimensional boundaries, unaffected 0-dimensional ones) lifts to
  --   the pasting of u↑ and w↑ through three associators.
  -- Anything else returns nothing, so the cylinder is not built.
  liftF : Nat → Ex → Maybe Ex
  liftF zero _ = nothing
  liftF (suc fl) (v i)      = if inY i then just (v (upl i)) else nothing
  liftF (suc fl) (idn e)    = nothing
  liftF (suc fl) (xc _ _)    = nothing
  liftF (suc fl) (xr _ _)    = nothing
  liftF (suc fl) (asL _ _ _) = nothing
  liftF (suc fl) (ru _)      = nothing
  liftF (suc fl) (lu _)      = nothing
  liftF (suc fl) (a1L _ _ _) = nothing
  liftF (suc fl) (a1R _ _ _) = nothing
  liftF (suc fl) (dw _ _ _)  = nothing
  liftF (suc fl) (dr _ _ _)  = nothing
  liftF (suc fl) (na _ _ _)  = nothing
  liftF (suc fl) (nr _ _ _)  = nothing
  liftF (suc fl) (ru2 _)     = nothing
  liftF (suc fl) (wi _ _)    = nothing
  liftF (suc fl) (hx _ _)    = nothing
  liftF (suc fl) (ru2r _)    = nothing
  liftF (suc fl) (wir _ _)   = nothing
  liftF (suc fl) (naD _ _ _) = nothing
  liftF (suc fl) (nrD _ _ _) = nothing
  liftF (suc fl) (hxD _ _)   = nothing
  liftF (suc fl) (asR _ _ _) = nothing
  liftF (suc fl) (bn k u w) =
    if affected u ∧ affected w then
      (if (suc k ==ℕ n) ∧ (n ==ℕ 2) ∧ (du ==ℕ 2) ∧ (dW ==ℕ 2) then paste else nothing)
    else if affected u then
      (if du ==ℕ n then (liftF fl u >>= λ u' → just (bn k u' (ren⁻ w)))
       else if (n ==ℕ 2) ∧ (du ==ℕ 1) ∧ (k ==ℕ 0)
       then (liftF fl u >>= λ u' → just (xc u' (ren⁻ w)))
       else nothing)
    else if affected w then
      (if dW ==ℕ n then (liftF fl w >>= λ w' → just (bn k (ren⁻ u) w'))
       else if (n ==ℕ 2) ∧ (dW ==ℕ 1) ∧ (k ==ℕ 0)
       then (liftF fl w >>= λ w' → just (xr (ren⁻ u) w'))
       else nothing)
    else nothing
    where
    du = dimΓ u
    dW = dimΓ w
    n  = max du dW
    srcΓ tgtΓ : Ex → Ex
    srcΓ e = srcE (tyE Γ e)
    tgtΓ e = tgtE (tyE Γ e)
    ok0 = not (affected (srcΓ (srcΓ u))) ∧ not (affected (tgtΓ (tgtΓ w)))
    ok1 = affected (srcΓ u) ∧ affected (tgtΓ u) ∧ affected (tgtΓ w)
    paste : Maybe Ex
    paste =
      if ok0 ∧ ok1 then
        (liftF fl u >>= λ u↑ → liftF fl w >>= λ w↑ →
         liftF fl (tgtΓ w) >>= λ Lτw → liftF fl (srcΓ w) >>= λ Lσw → liftF fl (srcΓ u) >>= λ Lσu →
         let u⁻ = ren⁻ u ; w⁻ = ren⁻ w ; u⁺ = ren⁺ u ; w⁺ = ren⁺ w in
         just (bn 2 (asL u⁻ w⁻ Lτw)
              (bn 2 (bn 1 u⁻ w↑)
              (bn 2 (asR u⁻ Lσw w⁺)
              (bn 2 (bn 1 u↑ w⁺)
                    (asL Lσu u⁺ w⁺))))))
      else nothing

  lift : Ex → Maybe Ex
  lift = liftF fuel

  -- a_x and b_x for x : A of dimension m ≥ 1, in the new context K.
  aSide bSide : Nat → Nat → Maybe Ex
  aSide x m = go m 0 (just (v (mi x)))
    where
    go : Nat → Nat → Maybe Ex → Maybe Ex
    go zero    j acc = acc
    go (suc f) j acc =
      if m ≤ℕ j then acc
      else go f (suc j)
        (acc >>= λ a →
          let w = tgtIter Γ (m ∸ j) (v x) in
          if affected w then (lift w >>= λ w' → just (bn j a w')) else just a)
  bSide x m = go m 0 (just (v (pl x)))
    where
    go : Nat → Nat → Maybe Ex → Maybe Ex
    go zero    j acc = acc
    go (suc f) j acc =
      if m ≤ℕ j then acc
      else go f (suc j)
        (acc >>= λ b →
          let w = srcIter Γ (m ∸ j) (v x) in
          if affected w then (lift w >>= λ w' → just (bn j w' b)) else just b)

  step : Nat → ExTy → ExCtx → Maybe ExCtx
  step x A K =
    if inY x then
      (if dimE A ==ℕ 0
       then just (K ++ (substTyE (λ i → v (mi i)) A ∷ substTyE (λ i → v (pl i)) A
                       ∷ hom ob (v (mi x)) (v (pl x)) ∷ []))
       else (aSide x (dimE A) >>= λ a → bSide x (dimE A) >>= λ b →
             let K' = K ++ (substTyE (λ i → v (mi i)) A ∷ substTyE (λ i → v (pl i)) A ∷ [])
             in just (K' ++ (hom (tyE K' a) a b ∷ []))))
    else just (K ++ (substTyE (λ i → v (mi i)) A ∷ []))

  walk : Nat → ExCtx → ExCtx → Maybe ExCtx
  walk x K []       = just K
  walk x K (A ∷ As) = step x A K >>= λ K' → walk (suc x) K' As

  cyl : Maybe Cyl
  cyl = walk 0 [] Γ >>= λ K →
        just (mkCyl K mi pl upl (map upl (filter inY (range (length Γ)))))

------------------------------------------------------------------------
-- Conical transfors: ctrf₁ Γ is the cylinder of the cone in the
-- direction of the projections (the diagram and the apex are fixed);
-- ctrf_{k+1} is the cylinder of ctrf_k in the direction of its newest
-- (top) variables. The comparison cells over positive-dimensional
-- diagram variables are the ones the repaired rules mark invertible.

record Ctrf : Set where
  constructor mkCtrf
  field
    ctx     : ExCtx
    topLvls : List Nat   -- the newest variables (one per variable of Γ)
    marked  : List Nat   -- every comparison variable over a positive-
                         -- dimensional variable of Γ, at every level
                         -- (the cone projections themselves stay lax)

ctrf : Nat → ExCtx → Maybe Ctrf
ctrf k Γ = go k (ConeOf.cone Γ) tops0 []
  where
  -- (level, is the diagram variable under it positive-dimensional?)
  tops0 : List (Nat × Bool)
  tops0 = map (λ x → suc (length Γ + x) , not (dimE (nth ob Γ x) ==ℕ 0)) (range (length Γ))
  go : Nat → ExCtx → List (Nat × Bool) → List Nat → Maybe Ctrf
  go zero    K tops mk = just (mkCtrf K (map fst tops) mk)
  go (suc j) K tops mk =
    CylOf.cyl K (map fst tops) >>= λ C →
    let ups  = map (λ t → Cyl.up C (fst t) , snd t) tops
        inY  = λ l → elem l (map fst tops)
        mk'  = concatMap (λ l → if inY l then (Cyl.minus C l ∷ Cyl.plus C l ∷ []) else (Cyl.minus C l ∷ [])) mk
             ++ map fst (filter snd ups)
    in go j (Cyl.ctx C) ups mk'

------------------------------------------------------------------------
-- Mikhail's (KE) side conditions, as an independent check that the
-- specified cone is one of the cones his judgment admits
-- (arXiv 2412.13310 §3.1; notes/limits-representables.md §2.1).
--
-- For a projection p_x : s → t, with Π the earlier projections:
--   FV(s : A) = {c} ∪ ⋃ { FV(p : T_p) | p ∈ Π, y ∈ FV(τx : ∂X), y ∝ τ(p) }
--   FV(t : A) = FV(x : X) ∪ ⋃ { FV(p : T_p) | p ∈ Π, y ∈ FV(σx : ∂X), y ∝ τ(p) }
--   x ∝ t
-- (for dim x = 0 the unions are empty).

module KE (Δ : Ctx) where
  dimTm : Tm → Nat
  dimTm (var i)              = dim (lookupTy Δ i)
  dimTm (coh _ (arr A _ _) _) = suc (dim A)
  dimTm _                    = 0

  subList : Sub → List Tm
  subList σ = go σ []
    where
    go : Sub → List Tm → List Tm
    go ⟨⟩       acc = acc
    go (σ ,ₛ t) acc = go σ (t ∷ acc)

  -- Linearity x ∝ t (Def. 3.1), requiring dim x = dim t at each step.
  mutual
    lin : Nat → Nat → Tm → Bool
    lin zero    x t = false
    lin (suc f) x t = (dim (lookupTy Δ x) ==ℕ dimTm t) ∧ linStr f x t

    linStr : Nat → Nat → Tm → Bool
    linStr f x (var y)       = x ==ℕ y
    linStr f x (coh P A σ)   = count (λ t → lin f x t) (subList σ) ==ℕ 1
    linStr f x (cst ())

  ∝ : Nat → Tm → Bool
  ∝ = lin fuel

  fvP : Nat → List Nat
  fvP p = fvTmTy (var p) (lookupTy Δ p)

  tgtOf : Nat → Tm
  tgtOf p with lookupTy Δ p
  ... | arr _ _ t = t
  ... | ⋆         = var p

  srcTyOf : Nat → Maybe (Tm × Ty)   -- (σx, ∂X)
  srcTyOf x with lookupTy Δ x
  ... | arr B s _ = just (s , B)
  ... | ⋆         = nothing
  tgtTyOf : Nat → Maybe (Tm × Ty)
  tgtTyOf x with lookupTy Δ x
  ... | arr B _ t = just (t , B)
  ... | ⋆         = nothing

  U : List Nat → Maybe (Tm × Ty) → List Nat
  U Π nothing        = []
  U Π (just (b , B)) =
    concatMap (λ p → if any (λ y → ∝ y (tgtOf p)) (fvTmTy b B) then fvP p else []) Π

  -- Check the projection at level ℓ over the diagram variable x.
  okProj : Nat → List Nat → Nat → Nat → Bool
  okProj c Π x ℓ with lookupTy Δ ℓ
  ... | arr A s t = ≈? (fvTmTy s A) (c ∷ U Π (tgtTyOf x))
                  ∧ ≈? (fvTmTy t A) (fvTmTy (var x) (lookupTy Δ x) ++ U Π (srcTyOf x))
                  ∧ ∝ x t
  ... | ⋆ = false

  -- All projections of a cone over an n-variable diagram.
  okConeAll : Nat → Bool
  okConeAll n = walk n 0 []
    where
    walk : Nat → Nat → List Nat → Bool
    walk zero    x Π = true
    walk (suc k) x Π = okProj n Π x (suc (n + x)) ∧ walk k (suc x) (Π ++ (suc (n + x) ∷ []))

------------------------------------------------------------------------
-- Dualities. O_J reverses the cells of every dimension in J. On the
-- expressions used here it is structural: a type of n-cells has its
-- source and target swapped when n ∈ J, and a composite along k-cells
-- has its factors swapped when k+1 ∈ J (Benjamin–Markakis, 2402.01611).
-- We use J = the odd dimensions.

oddJ : Nat → Bool
oddJ zero          = false
oddJ (suc zero)    = true
oddJ (suc (suc n)) = oddJ n

dualE : Ex → Ex
dualE (v i)      = v i
dualE (idn e)    = idn (dualE e)
dualE (bn k u w) = if oddJ (suc k) then bn k (dualE w) (dualE u) else bn k (dualE u) (dualE w)
-- O_odd swaps ∗₀ factors and the ends of 3-cells, and fixes ∗₁:
-- the dual of an interchange is the interchange with factors swapped,
-- and the dual of an associator is the reverse associator.
dualE (xc u w)    = xc (dualE w) (dualE u)
dualE (xr u w)    = xr (dualE w) (dualE u)
-- O_odd reverses 1-cells and swaps ∗₀ factors; 2-cells keep their
-- direction. So a right unitor becomes a left one, and the associator of
-- 1-cells becomes the reverse associator of the swapped factors.
dualE (ru w)      = lu (dualE w)
dualE (lu w)      = ru (dualE w)
dualE (a1L u y w) = a1R (dualE w) (dualE y) (dualE u)
dualE (a1R u y w) = a1L (dualE w) (dualE y) (dualE u)
-- The coherences used for cones over 2-dimensional terms have no dual
-- constructors yet. dualE leaves them unchanged, and coconeT refuses
-- (returns nothing) when a cone contains one; see dualOK.
-- The 2-dimensional cone cells: each dual is the paired cell above
-- (O_odd swaps ∗₀ factors, turns a1L into a1R, and reverses 3-cells).
dualE (dw u a b) = dr (dualE a) (dualE b) (dualE u)
dualE (dr a b u) = dw (dualE u) (dualE a) (dualE b)
dualE (na u a w) = naD (dualE w) (dualE a) (dualE u)
dualE (naD w a u) = na (dualE u) (dualE a) (dualE w)
dualE (nr u w b) = nrD (dualE b) (dualE w) (dualE u)
dualE (nrD b w u) = nr (dualE u) (dualE w) (dualE b)
dualE (ru2 a)    = ru2r (dualE a)
dualE (ru2r a)   = ru2 (dualE a)
dualE (wi u w)   = wir (dualE w) (dualE u)
dualE (wir w u)  = wi (dualE u) (dualE w)
dualE (hx a b)   = hxD (dualE b) (dualE a)
dualE (hxD b a)  = hx (dualE a) (dualE b)
dualE (asL u y w) = asR (dualE u) (dualE y) (dualE w)
dualE (asR u y w) = asL (dualE u) (dualE y) (dualE w)

dualTy : ExTy → ExTy
dualTy ob          = ob
dualTy (hom A s t) =
  if oddJ (dimE (hom A s t)) then hom (dualTy A) (dualE t) (dualE s)
  else hom (dualTy A) (dualE s) (dualE t)

dualCtx : ExCtx → ExCtx
dualCtx = map dualTy

-- Cocone transfors: the O_odd-dual of the cone transfors of the dual
-- diagram. This gives the diagram-index-first Gray order required for
-- colimits (notes/limits-metatheory.md §8.2):
--   m_f : m_x ∗₁ q′_f ⇛ q_f ∗₁ (f ∗₀ m_y).
coctrf : Nat → ExCtx → Maybe Ctrf
coctrf k Γ = ctrf k (dualCtx Γ) >>= λ T →
             just (mkCtrf (dualCtx (Ctrf.ctx T)) (Ctrf.topLvls T) (Ctrf.marked T))

------------------------------------------------------------------------
-- Free object = lax colimit of the point, for 1-dimensional Γ (B6).
--
-- ΣΓ := susp Γ is the context of Γ-families of elements: ⊤, c, and
-- s_x : ⊤ → c, s_f : s_x ⇒ s_y. K := constCocone Γ is the constant
-- instance of the specified cocone: q_x : ⊤ → c, q_f : q_x ⇒ id_⊤ ∗₀ q_y.
-- Levels: ⊤ = 0, c = 1, and the variable over x ∈ Γ at level 2 + x in
-- both. We give
--   φ : ΣΓ ⊢ φ : K      (a family is a cocone)
--   ψ : K ⊢ ψ : ΣΓ      (a cocone is a family)
--   H  : ΣΓ ⊢ H  : ΣΓ↑Y   with H⁻ = ψ∘φ, H⁺ = id
--   H′ : K  ⊢ H′ : K↑Y    with H′⁻ = φ∘ψ, H′⁺ = id
-- where Y is everything but ⊤ and c. Every component of H and H′ is a
-- coherence, an identity, or a composite of whiskered coherences, hence
-- invertible (Benjamin–Markakis–Sarti). The paper proof that these are
-- well typed for every 1-dimensional Γ is notes/specified-cones.md §6;
-- the checker confirms it on the shapes in ConesExamples.

module ConstPoint (Γ : ExCtx) where
  private
    D¹ D² V3 : Ctx
    D¹ = Disk 1
    D² = Disk 2
    -- three vertically composable 2-cells
    V3 = ctxOf (node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ []))

    cohC : Ctx → Ty → List Tm → Cell
    cohC P A ts = coh P A ⟪ ts ⟫ , A [ ⟪ ts ⟫ ]ty

    asTy : Cell → Cell → Ty      -- the type s → t of parallel cells
    asTy s t = arr (snd s) (fst s) (fst t)

    -- In D¹ = (x₀, y₀, w): the unitor λ : id ∗₀ w ⇒ w and its inverse.
    x₀ y₀ : Cell
    x₀ = gen D¹ 0
    y₀ = gen D¹ 1
    idw : Cell                       -- id_{x₀} ∗₀ w
    idw = binC 0 (idC x₀) (gen D¹ 2)
    λT λiT : Ty
    λT  = asTy idw (gen D¹ 2)
    λiT = asTy (gen D¹ 2) idw
    
  -- λ and λ⁻¹ at a 1-cell (any context).
  lam lami : Cell → Cell
  lam  w = cohC D¹ λT  (diskList w)
  lami w = cohC D¹ λiT (diskList w)

  private
    -- Generic cells of D² = (x₀, y₀, a, b, u : a ⇒ b).
    gA gB gU : Cell
    gA = gen D² 2
    gB = gen D² 3
    gU = gen D² 4
    idB : Cell                       -- id_{x₀} ∗₀ b in D²
    idB = binC 0 (idC (gen D² 0)) gB
    -- The unary operation U : a ⇒ id ∗₀ b over D² (operation case:
    -- the source uses exactly ∂⁻D², the target exactly ∂⁺D²).
    UT : Ty
    UT = asTy gA idB
    Ugen : Cell
    Ugen = cohC D² UT (map var (range 5))
    lamB lamiB : Cell
    lamB  = lam gB
    lamiB = lami gB

  -- U applied to a 2-cell u : a ⇒ b.
  Uop : Cell → Cell
  Uop u = cohC D² UT (diskList u)

  n = length Γ
  isOb : Nat → Bool
  isOb x = dimE (nth ob Γ x) ==ℕ 0
  bnd : Nat → Nat × Nat
  bnd x = idxE (srcE (nth ob Γ x)) , idxE (tgtE (nth ob Γ x))

  ΣΓ 𝒦 : Ctx
  ΣΓ = evCtx (susp Γ)
  𝒦  = evCtx (constCocone Γ)

  cellΣ cellK : Nat → Cell     -- the variable over x
  cellΣ x = gen ΣΓ (2 + x)
  cellK x = gen 𝒦 (2 + x)

  -- φ: ⊤, c, q_x ↦ s_x, q_f ↦ U(s_f).
  φ : Sub
  φ = ⟪ var 0 ∷ var 1 ∷ map (λ x → if isOb x then var (2 + x) else fst (Uop (cellΣ x))) (range n) ⟫

  -- ψ: ⊤, c, s_x ↦ q_x, s_f ↦ q_f ∗₁ λ_{q_y}.
  ψf : Nat → Cell
  ψf x = binC 1 (cellK x) (lam (cellK (snd (bnd x))))

  ψ : Sub
  ψ = ⟪ var 0 ∷ var 1 ∷ map (λ x → if isOb x then var (2 + x) else fst (ψf x)) (range n) ⟫

  Y : List Nat
  Y = rangeFrom 2 n

  -- Components of H over s_f, generically in D²:
  --   (U(u) ∗₁ λ_b) ∗₁ id_b  ⇛  id_a ∗₁ u          (full coherence)
  private
    HgenT : Ty
    HgenT = asTy (binC 1 (binC 1 Ugen lamB) (idC gB)) (binC 1 (idC gA) gU)

  Hf : Nat → Cell
  Hf x = cohC D² HgenT (diskList (cellΣ x))

  -- Components of H′ over q_f: c₁ ∗₂ c₂ ∗₂ (q_f ∗₁ c₃) ∗₂ c₄.
  private
    -- c₁ over D² (u ↦ ψ(s_f)):  U(u) ∗₁ (id_{x₀} ∗₀ id_b) ⇛ u ∗₁ λ⁻¹_b
    c₁T : Ty
    c₁T = asTy (binC 1 Ugen (binC 0 (idC (gen D² 0)) (idC gB))) (binC 1 gU lamiB)
    -- c₂ over V3: (u ∗₁ v) ∗₁ v′ ⇛ u ∗₁ (v ∗₁ v′)
    c₂T : Ty
    c₂T = asTy (binC 1 (binC 1 (gen V3 4) (gen V3 6)) (gen V3 8))
               (binC 1 (gen V3 4) (binC 1 (gen V3 6) (gen V3 8)))
    -- c₃ over D¹: λ_w ∗₁ λ⁻¹_w ⇛ id_{id ∗₀ w}
    c₃T : Ty
    c₃T = asTy (binC 1 (lam (gen D¹ 2)) (lami (gen D¹ 2))) (idC idw)
    -- c₄ over D²: u ∗₁ id_b ⇛ id_a ∗₁ u
    c₄T : Ty
    c₄T = asTy (binC 1 gU (idC gB)) (binC 1 (idC gA) gU)

  H′f : Nat → Cell
  H′f x = binC 2 (binC 2 (binC 2 c₁ c₂) (binC 1 qf c₃)) c₄
    where
    qf = cellK x
    qy = cellK (snd (bnd x))
    idqy = binC 0 (idC (gen 𝒦 0)) qy
    c₁ = cohC D² c₁T (diskList (ψf x))
    c₂ = cohC V3 c₂T (fst (gen 𝒦 0) ∷ fst (gen 𝒦 1) ∷ fst (cellK (fst (bnd x)))
                       ∷ fst idqy ∷ fst qf ∷ fst qy ∷ fst (lam qy) ∷ fst idqy ∷ fst (lami qy) ∷ [])
    c₃ = cohC D¹ c₃T (diskList qy)
    c₄ = cohC D² c₄T (diskList qf)

  -- The homotopies as substitutions into the cylinder contexts. The
  -- cylinder layout keeps ⊤ and c, then for each x: x⁻, x⁺, x↑.
  H H′ : Sub
  H  = ⟪ var 0 ∷ var 1 ∷ concatMap (λ x →
          lookupₛ (ψ ∘ φ) (2 + x) ∷ var (2 + x)
          ∷ (if isOb x then fst (idC (cellΣ x)) else fst (Hf x)) ∷ []) (range n) ⟫
  H′ = ⟪ var 0 ∷ var 1 ∷ concatMap (λ x →
          lookupₛ (φ ∘ ψ) (2 + x) ∷ var (2 + x)
          ∷ (if isOb x then fst (idC (cellK x)) else fst (H′f x)) ∷ []) (range n) ⟫

  cylΣ cylK : Maybe Ctx
  cylΣ = CylOf.cyl (susp Γ) Y >>= λ C → just (evCtx (Cyl.ctx C))
  cylK = CylOf.cyl (constCocone Γ) Y >>= λ C → just (evCtx (Cyl.ctx C))

  -- Decisions, each backed by the certified checker.
  okφ okψ okH okH′ : Bool
  okφ = is-just (checkCtx ΣΓ >>= λ w → checkSub ΣΓ w φ 𝒦)
  okψ = is-just (checkCtx 𝒦 >>= λ w → checkSub 𝒦 w ψ ΣΓ)
  okH = okSub ΣΓ H cylΣ
    where
    okSub : (Γ' : Ctx) → Sub → Maybe Ctx → Bool
    okSub Γ' σ nothing  = false
    okSub Γ' σ (just C) = is-just (checkCtx Γ' >>= λ w → checkSub Γ' w σ C)
  okH′ = okSub 𝒦 H′ cylK
    where
    okSub : (Γ' : Ctx) → Sub → Maybe Ctx → Bool
    okSub Γ' σ nothing  = false
    okSub Γ' σ (just C) = is-just (checkCtx Γ' >>= λ w → checkSub Γ' w σ C)

------------------------------------------------------------------------
-- φ for every globular Γ: "a family is a cocone" in all dimensions.
--
-- For a variable t of dimension m ≥ 1, the constant-cocone type of q_t,
-- pushed along φ (already defined on lower variables), is A → B with
-- Var(A) = ∂⁻ and Var(B) = ∂⁺ of the disk around s_t. So it is the type
-- of an operation-case coherence over that disk D^{m+1} = ΣD^m:
--     φ(q_t) := coh_{D^{m+1}, A → B}[χ_t].
-- The generic type is computed once per dimension, in the disk itself.

module PhiAll where
  private
    dTy : Nat → ExTy
    dTy zero    = ob
    dTy (suc j) = hom (dTy j) (v (j + j)) (v (suc (j + j)))
    dEx : Nat → ExCtx
    dEx n = concatMap (λ j → dTy j ∷ dTy j ∷ []) (range n) ++ (dTy n ∷ [])
    -- φ on the generic disk Γ = D^m, as a list of ΣD^m-terms for the
    -- K(D^m) variables, computed for all variables below the top one.
    -- genTyF f m: the type of φ(q_top) in ΣD^m = D^{m+1} (f is fuel ≥ m).
    mutual
      genTyF : Nat → Nat → Ty
      genTyF zero    m = ⋆
      genTyF (suc f) m = lookupTy (evCtx (constCocone (dEx m))) (2 + (m + m)) [ φdisk f m ]ty

      φdisk : Nat → Nat → Sub
      φdisk f m = ⟪ var 0 ∷ var 1 ∷ map (φvar f m) (range (m + m)) ⟫

      φvar : Nat → Nat → Nat → Tm
      φvar f m x = phiAt f (dimE (nth ob (dEx m) x)) (evCtx (susp (dEx m))) x

      phiAt : Nat → Nat → Ctx → Nat → Tm
      phiAt f zero    S x = var (2 + x)
      phiAt f (suc j) S x = coh (Disk (suc (suc j))) (genTyF f (suc j)) ⟪ diskList (gen S (2 + x)) ⟫

  genTy : Nat → Ty
  genTy m = genTyF (suc m) m

  -- φ for an arbitrary globular Γ.
  φ : ExCtx → Sub
  φ Γ = ⟪ var 0 ∷ var 1 ∷ map φv (range (length Γ)) ⟫
    where
    S = evCtx (susp Γ)
    φv : Nat → Tm
    φv x with dimE (nth ob Γ x)
    ... | zero  = var (2 + x)
    ... | suc j = coh (Disk (suc (suc j))) (genTy (suc j)) ⟪ diskList (gen S (2 + x)) ⟫

  okφ : ExCtx → Bool
  okφ Γ = is-just (checkCtx S >>= λ w → checkSub S w (φ Γ) (evCtx (constCocone Γ)))
    where S = evCtx (susp Γ)

------------------------------------------------------------------------
-- B6 in dimension 2 (ledger B20): ψ and the homotopy H for globular Γ
-- of dimension ≤ 2. The homotopy H′ on the cocone side is not here: it
-- needs the cylinder on 𝒦 over 2-cells, whose lift of id²_⊤ ∗₀ q_y is a
-- mirrored interchange (see notes/specified-cones.md §6.4).

module PsiD2 (Γ : ExCtx) where
  open ConstPoint Γ public using (lam; lami; ΣΓ; 𝒦; cellΣ; cellK; bnd; ψf; Hf; Y; cylΣ)

  dimV : Nat → Nat
  dimV x = dimE (nth ob Γ x)

  cohC : Ctx → Ty → List Tm → Cell
  cohC P A ts = coh P A ⟪ ts ⟫ , A [ ⟪ ts ⟫ ]ty

  asTy : Cell → Cell → Ty
  asTy s t = arr (snd s) (fst s) (fst t)

  -- κ' over D¹ = (x₀, y₀, w):  λ_w ⇛ (id_{id_{x₀}} ∗₀ w) ∗₁ λ_w  (full coherence).
  private
    D¹ : Ctx
    D¹ = Disk 1
    w₀ : Cell
    w₀ = gen D¹ 2
    κT : Ty
    κT = asTy (lam w₀) (binC 1 (binC 0 (idC (idC (gen D¹ 0))) w₀) (lam w₀))

  -- For α : f ⇒ g with f, g : x → y, the constant cocone has
  --   q_α : q_f ∗₁ (id²_⊤ ∗₀ q_y) ⇛ q_g.
  -- ψ(s_α) : q_f ∗₁ λ ⇛ q_g ∗₁ λ is
  --   (q_f ∗₁ κ') ∗₂ assoc⁻¹(q_f, id²_⊤ ∗₀ q_y, λ) ∗₂ (q_α ∗₁ λ).
  ψα : Nat → Cell
  ψα x = binC 2 (binC 2 (binC 1 qf κ') (assocC false qf W (lam qy))) (binC 1 qα (lam qy))
    where
    f  = fst (bnd x)
    qα = cellK x
    qf = cellK f
    qy = cellK (snd (bnd f))
    W  = binC 0 (idC (idC (gen 𝒦 0))) qy
    κ' = cohC D¹ κT (diskList qy)

  φ : Sub
  φ = PhiAll.φ Γ

  ψ : Sub
  ψ = ⟪ var 0 ∷ var 1 ∷ map ψv (range (length Γ)) ⟫
    where
    ψv : Nat → Tm
    ψv x with dimV x
    ... | zero        = var (2 + x)
    ... | suc zero    = fst (ψf x)
    ... | suc (suc _) = fst (ψα x)

  ψφ : Sub
  ψφ = ψ ∘ φ

-- The generic H-component over a 2-cell, computed once in ΣD² = D³:
--   (ψφ(s_α) ∗₁ id_{s_y}) ∗₂ H_g  ⇛  H_f ∗₂ (id_{s_x} ∗₁ s_α),
-- a full coherence over D³ (both sides use every variable).
module HGenD2 where
  G : ExCtx
  G = ob ∷ ob ∷ hom ob (v 0) (v 1) ∷ hom ob (v 0) (v 1) ∷ hom (hom ob (v 0) (v 1)) (v 2) (v 3) ∷ []
  open PsiD2 G
  S : Ctx
  S = ΣΓ
  sα : Cell
  sα = gen S 6
  ψφα : Cell
  ψφα = lookupₛ ψφ 6 , lookupTy S 6 [ ψφ ]ty
  a b : Cell
  a = binC 2 (binC 1 ψφα (idC (gen S 3))) (Hf 3)
  b = binC 2 (Hf 2) (binC 1 (idC (gen S 2)) sα)
  HαT : Ty
  HαT = asTy a b

module ConstD2 (Γ : ExCtx) where
  open PsiD2 Γ public

  Hα : Nat → Cell
  Hα x = cohC HGenD2.S HGenD2.HαT (diskList (cellΣ x))

  H : Sub
  H = ⟪ var 0 ∷ var 1 ∷ concatMap (λ x → lookupₛ ψφ (2 + x) ∷ var (2 + x) ∷ comp x ∷ []) (range (length Γ)) ⟫
    where
    comp : Nat → Tm
    comp x with dimV x
    ... | zero        = fst (idC (cellΣ x))
    ... | suc zero    = fst (Hf x)
    ... | suc (suc _) = fst (Hα x)

  okψ okH : Bool
  okψ = is-just (checkCtx 𝒦 >>= λ w → checkSub 𝒦 w ψ ΣΓ)
  okH = okSub cylΣ
    where
    okSub : Maybe Ctx → Bool
    okSub nothing  = false
    okSub (just C) = is-just (checkCtx ΣΓ >>= λ w → checkSub ΣΓ w H C)

-- Cocones over 1-dimensional coherence terms, as the O_odd dual of the
-- cone over the dual diagram (on globular Γ this is CoconeOf.cocone).
dualOK : Ex → Bool
dualOK (v _)       = true
dualOK (bn _ u w)  = dualOK u ∧ dualOK w
dualOK (idn e)     = dualOK e
dualOK (xc u w)    = dualOK u ∧ dualOK w
dualOK (xr u w)    = dualOK u ∧ dualOK w
dualOK (asL u y w) = dualOK u ∧ dualOK y ∧ dualOK w
dualOK (asR u y w) = dualOK u ∧ dualOK y ∧ dualOK w
dualOK (ru w)      = dualOK w
dualOK (lu w)      = dualOK w
dualOK (a1L u y w) = dualOK u ∧ dualOK y ∧ dualOK w
dualOK (a1R u y w) = dualOK u ∧ dualOK y ∧ dualOK w
dualOK (dw u a b)  = dualOK u ∧ dualOK a ∧ dualOK b
dualOK (dr a b u)  = dualOK a ∧ dualOK b ∧ dualOK u
dualOK (na u a w)  = dualOK u ∧ dualOK a ∧ dualOK w
dualOK (naD w a u) = dualOK w ∧ dualOK a ∧ dualOK u
dualOK (nr u w b)  = dualOK u ∧ dualOK w ∧ dualOK b
dualOK (nrD b w u) = dualOK b ∧ dualOK w ∧ dualOK u
dualOK (ru2 a)     = dualOK a
dualOK (ru2r a)    = dualOK a
dualOK (wi u w)    = dualOK u ∧ dualOK w
dualOK (wir w u)   = dualOK w ∧ dualOK u
dualOK (hx a b)    = dualOK a ∧ dualOK b
dualOK (hxD b a)   = dualOK b ∧ dualOK a

dualOKTy : ExTy → Bool
dualOKTy ob          = true
dualOKTy (hom A s t) = dualOKTy A ∧ dualOK s ∧ dualOK t

coconeT : ExCtx → Maybe ExCtx
coconeT Γ = ConeT.cone (dualCtx Γ) >>= λ K →
            if all dualOKTy K then just (dualCtx K) else nothing
