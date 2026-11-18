------------------------------------------------------------------------
-- A small *uncertified* elaborator for raw CaTT terms.
--
-- Everything here is a meta-program producing raw syntax: type
-- inference that trusts the input, the standard whiskerings and
-- unbiased composites as coh terms, and a function that fills in a
-- substitution into a pasting scheme from the images of its locally
-- maximal variables. Nothing produced here is trusted: every result
-- used as evidence elsewhere is re-checked by the certified checker
-- (CaTTExp.Check), which returns a typing derivation.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Elab where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import Agda.Builtin.Nat using (_*_)

infixl 4 _<$>_
_<$>_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
f <$> nothing = nothing
f <$> just x  = just (f x)

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (_ ∷ xs) = suc (length xs)

replicate : ∀ {a} {A : Set a} → Nat → A → List A
replicate zero    _ = []
replicate (suc n) x = x ∷ replicate n x

mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → Maybe B) → List A → Maybe (List B)
mapM f []       = just []
mapM f (x ∷ xs) = f x >>= λ y → mapM f xs >>= λ ys → just (y ∷ ys)

------------------------------------------------------------------------
-- Trees for the standard shapes.

-- The n-globe Dⁿ.
chain : Nat → Tree
chain zero    = leaf
chain (suc n) = node (chain n ∷ [])

-- Put a tree k levels up: wrap k t lives in an iterated hom.
wrap : Nat → Tree → Tree
wrap zero    t = t
wrap (suc k) t = node (wrap k t ∷ [])

-- The locally maximal variables of ctxOf t, left to right, as levels.
-- (Simulates the pse/psd run of PastingTrees.build.)
mutual
  topsF : Nat → List Tree → List Nat × Nat
  topsF L []               = [] , L
  topsF L (node [] ∷ ts)   = let r = topsF (suc (suc L)) ts in (suc L ∷ fst r) , snd r
  topsF L (node (c ∷ cs) ∷ ts) =
    let r₁ = topsF (suc (suc L)) (c ∷ cs)
        r₂ = topsF (snd r₁) ts
    in (fst r₁ ++ fst r₂) , snd r₂

tops : Tree → List Nat
tops (node []) = 0 ∷ []
tops (node ts) = fst (topsF 1 ts)

------------------------------------------------------------------------
-- Type inference on raw terms. Trusts its input.

tyOf : Ctx → Tm → Maybe Ty
tyOf Γ (var i)     = lookup Γ i
tyOf Γ (coh _ A σ) = just (A [ σ ]ty)
tyOf Γ (cst ())

dimOf : Ctx → Tm → Maybe Nat
dimOf Γ t = dim <$> tyOf Γ t

srcOf tgtOf : Ctx → Tm → Maybe Tm
srcOf Γ t = tyOf Γ t >>= λ where
  (arr _ s _) → just s
  ⋆           → nothing
tgtOf Γ t = tyOf Γ t >>= λ where
  (arr _ _ u) → just u
  ⋆           → nothing

------------------------------------------------------------------------
-- Filling a substitution into a pasting scheme P from the images of
-- its locally maximal variables: every other variable of P is an
-- iterated source or target of one of those, so its image is read off
-- from the inferred type of the image. Inconsistent images are not
-- detected here; the certified checker rejects them.

Assign : Set
Assign = List (Nat × Tm)

unify : Ty → Ty → Maybe Assign
unify ⋆ ⋆ = just []
unify (arr A (var a) (var b)) (arr B s t) =
  unify A B >>= λ as → just ((a , s) ∷ (b , t) ∷ as)
unify _ _ = nothing

findA : Assign → Nat → Maybe Tm
findA []             n = nothing
findA ((m , t) ∷ as) n = if n ==ℕ m then just t else findA as n

subOf : Nat → Assign → Maybe Sub
subOf zero    as = just ⟨⟩
subOf (suc n) as = subOf n as >>= λ σ → findA as n >>= λ t → just (σ ,ₛ t)

zipA : List Nat → List Tm → Maybe Assign
zipA []       []       = just []
zipA (n ∷ ns) (t ∷ ts) = zipA ns ts >>= λ as → just ((n , t) ∷ as)
zipA _        _        = nothing

fill : Ctx → Ctx → Assign → Maybe Sub
fill Γ P top = go top >>= λ rest → subOf (len P) (top ++ rest)
  where
  go : Assign → Maybe Assign
  go []             = just []
  go ((p , u) ∷ as) =
    lookup P p >>= λ B' → tyOf Γ u >>= λ B → unify B' B >>= λ bs →
    go as >>= λ cs → just (bs ++ cs)

-- The general coh former: a pasting scheme T, a builder that produces
-- the source and target *inside* ctxOf T, and the images (in Γ) of the
-- locally maximal variables of T, in order.
cohT : Ctx → Tree → (Ctx → Maybe (Tm × Tm)) → List Tm → Maybe Tm
cohT Γ T build cells =
  let P = ctxOf T in
  build P >>= λ st →
  tyOf P (fst st) >>= λ A →
  zipA (tops T) cells >>= λ top →
  fill Γ P top >>= λ σ →
  just (coh P (arr A (fst st) (snd st)) σ)

------------------------------------------------------------------------
-- Whiskering and unbiased composites.

private
  srcTgtVar : Ctx → Nat → Maybe (Nat × Nat)
  srcTgtVar P l = lookup P l >>= λ where
    (arr _ (var a) (var b)) → just (a , b)
    _                       → nothing

  topN : Tree → Nat → Nat
  topN T i = go (tops T) i
    where
    go : List Nat → Nat → Nat
    go []       _       = 0
    go (x ∷ _)  zero    = x
    go (_ ∷ xs) (suc i) = go xs i

mutual
  -- c ▹ z: c an n-cell, z a (k+1)-cell whose k-source is the k-target
  -- of c (k < n). For n = k+1 this is binary composition along k.
  rw : Nat → Ctx → Tm → Tm → Maybe Tm
  rw zero       Γ c z = nothing
  rw (suc fuel) Γ c z =
    dimOf Γ c >>= λ n → dimOf Γ z >>= λ where
      zero      → nothing
      (suc k)   → guard (k <ℕ n) λ _ →
        let T  = wrap k (node (chain (n ∸ suc k) ∷ leaf ∷ []))
            cL = topN T 0
            zL = topN T 1
        in cohT Γ T (λ P →
             srcTgtVar P cL >>= λ ab → srcTgtVar P zL >>= λ dw →
             if n ==ℕ suc k
             then just (var (fst ab) , var (snd dw))
             else (rw fuel P (var (fst ab)) (var zL) >>= λ s →
                   rw fuel P (var (snd ab)) (var zL) >>= λ t → just (s , t)))
           (c ∷ z ∷ [])

  -- z ◃ c: z a (k+1)-cell whose k-target is the k-source of the n-cell c.
  lw : Nat → Ctx → Tm → Tm → Maybe Tm
  lw zero       Γ z c = nothing
  lw (suc fuel) Γ z c =
    dimOf Γ c >>= λ n → dimOf Γ z >>= λ where
      zero      → nothing
      (suc k)   → guard (k <ℕ n) λ _ →
        let T  = wrap k (node (leaf ∷ chain (n ∸ suc k) ∷ []))
            zL = topN T 0
            cL = topN T 1
        in cohT Γ T (λ P →
             srcTgtVar P zL >>= λ dw → srcTgtVar P cL >>= λ ab →
             if n ==ℕ suc k
             then just (var (fst dw) , var (snd ab))
             else (lw fuel P (var zL) (var (fst ab)) >>= λ s →
                   lw fuel P (var zL) (var (snd ab)) >>= λ t → just (s , t)))
           (z ∷ c ∷ [])

-- Unbiased composite of a nonempty list of n-cells along n−1 (n ≥ 1).
-- A one-element list is returned unchanged.
vcomp : Ctx → List Tm → Maybe Tm
vcomp Γ []          = nothing
vcomp Γ (c ∷ [])    = just c
vcomp Γ (c ∷ d ∷ cs) =
  dimOf Γ c >>= λ where
    zero    → nothing
    (suc k) →
      let T  = wrap k (node (replicate (length (c ∷ d ∷ cs)) leaf))
          ts = tops T
      in cohT Γ T (λ P → first ts >>= λ f → last ts >>= λ l →
                     srcTgtVar P f >>= λ s → srcTgtVar P l >>= λ t →
                     just (var (fst s) , var (snd t)))
                  (c ∷ d ∷ cs)
  where
  first last : List Nat → Maybe Nat
  first []       = nothing
  first (x ∷ _)  = just x
  last []        = nothing
  last (x ∷ [])  = just x
  last (_ ∷ x ∷ xs) = last (x ∷ xs)

-- Default fuel: whiskering recursion depth is bounded by dimension.
F : Nat
F = 16

_▹_ : Ctx → Tm → Tm → Maybe Tm
(Γ ▹ c) z = rw F Γ c z

_◃_ : Ctx → Tm → Tm → Maybe Tm
(Γ ◃ z) c = lw F Γ z c

------------------------------------------------------------------------
-- Coherences over the 1-dimensional chain Comp₃: associators.

Comp₃T : Tree
Comp₃T = node (leaf ∷ leaf ∷ leaf ∷ [])

-- assoc f g h : (f;g);h ⇒ f;(g;h)
assoc assoc⁻ : Ctx → Tm → Tm → Tm → Maybe Tm
assoc Γ f g h = cohT Γ Comp₃T (λ P →
    vcomp P (var 2 ∷ var 4 ∷ []) >>= λ fg → vcomp P (fg ∷ var 6 ∷ []) >>= λ l →
    vcomp P (var 4 ∷ var 6 ∷ []) >>= λ gh → vcomp P (var 2 ∷ gh ∷ []) >>= λ r →
    just (l , r))
  (f ∷ g ∷ h ∷ [])
assoc⁻ Γ f g h = cohT Γ Comp₃T (λ P →
    vcomp P (var 2 ∷ var 4 ∷ []) >>= λ fg → vcomp P (fg ∷ var 6 ∷ []) >>= λ l →
    vcomp P (var 4 ∷ var 6 ∷ []) >>= λ gh → vcomp P (var 2 ∷ gh ∷ []) >>= λ r →
    just (r , l))
  (f ∷ g ∷ h ∷ [])

------------------------------------------------------------------------
-- Rewriting inside a vertical chain of n-cells by an (n+1)-cell.
--
-- Given a chain pre ++ seg ++ post of n-cells (composed along n−1) and
-- Φ : vcomp seg → vcomp seg', `stepAt` builds the (n+1)-cell
--   vcomp (pre ++ seg ++ post) → vcomp (pre ++ seg' ++ post)
-- as regroup ; whisker Φ ; regroup. Regroupings are full coherences
-- over the chain pasting scheme; the whiskering is an operation.

private
  splitAt : ∀ {a} {A : Set a} → Nat → List A → List A × List A
  splitAt zero    xs       = [] , xs
  splitAt (suc n) []       = [] , []
  splitAt (suc n) (x ∷ xs) = let r = splitAt n xs in (x ∷ fst r) , snd r

  vars : List Nat → List Tm
  vars []       = []
  vars (n ∷ ns) = var n ∷ vars ns

-- vcomp (pre ++ mid ++ post) → vcomp (pre ++ [vcomp mid] ++ post), and back.
regroup : Bool → Ctx → List Tm → List Tm → List Tm → Maybe Tm
regroup dir Γ pre mid post =
  dm >>= λ where
    zero    → nothing
    (suc k) →
      let T  = wrap k (node (replicate (length cs₀) leaf))
          ts = vars (tops T)
          p  = splitAt (length pre) ts
          q  = splitAt (length mid) (snd p)
      in cohT Γ T (λ P →
           vcomp P ts >>= λ flat →
           vcomp P (fst q) >>= λ m →
           vcomp P (fst p ++ (m ∷ snd q)) >>= λ grp →
           just (if dir then (flat , grp) else (grp , flat)))
         cs₀
  where
  cs₀ = pre ++ mid ++ post
  dm : Maybe Nat
  dm = hd cs₀ >>= dimOf Γ
    where
    hd : List Tm → Maybe Tm
    hd []      = nothing
    hd (x ∷ _) = just x

-- whisker an (n+1)-cell Φ : s → t into position |pre| of a chain.
whiskIn : Ctx → List Tm → Tm → List Tm → Maybe Tm
whiskIn Γ [] Φ [] = just Φ
whiskIn Γ pre Φ post =
  dimOf Γ Φ >>= λ where
    zero          → nothing
    (suc zero)    → nothing
    (suc (suc k)) →
      let T = wrap k (node (replicate (length pre) leaf ++
                            (node (leaf ∷ []) ∷ replicate (length post) leaf)))
          ts = vars (tops T)
          p  = splitAt (length pre) ts
          rest = snd p
      in cohT Γ T (λ P → hd rest >>= λ φ → srcOf P φ >>= λ s → tgtOf P φ >>= λ t →
                     vcomp P (fst p ++ s ∷ tl rest) >>= λ l →
                     vcomp P (fst p ++ t ∷ tl rest) >>= λ r →
                     just (l , r))
                  (pre ++ Φ ∷ post)
  where
  hd : List Tm → Maybe Tm
  hd []      = nothing
  hd (x ∷ _) = just x
  tl : List Tm → List Tm
  tl []       = []
  tl (_ ∷ xs) = xs

stepAt : Ctx → List Tm → List Tm → List Tm → Tm → List Tm → Maybe (List Tm × Tm)
stepAt Γ pre seg post Φ seg' =
  whiskIn Γ pre Φ post >>= λ w →
  pieces w >>= λ ps → vcomp Γ ps >>= λ cell →
  just ((pre ++ seg' ++ post) , cell)
  where
  one : List Tm → Bool
  one (_ ∷ []) = true
  one _        = false
  pieces : Tm → Maybe (List Tm)
  pieces w =
    (if one seg then just [] else ((λ r → r ∷ []) <$> regroup true Γ pre seg post)) >>= λ a →
    (if one seg' then just [] else ((λ r → r ∷ []) <$> regroup false Γ pre seg' post)) >>= λ b →
    just (a ++ (w ∷ b))

------------------------------------------------------------------------
-- Identities, cancellation of associators, and unitors.

-- The identity on an n-cell u, as the coherence over Dⁿ.
idc : Ctx → Tm → Maybe Tm
idc Γ u = dimOf Γ u >>= λ n →
  cohT Γ (chain n) (λ P → just (var (n + n) , var (n + n))) (u ∷ [])

-- assoc ; assoc⁻ ⇒ id  (dir = true)  or  id ⇒ assoc ; assoc⁻  (dir = false).
-- With inv = true the associators are swapped: assoc⁻ ; assoc.
cancel : Bool → Bool → Ctx → Tm → Tm → Tm → Maybe Tm
cancel inv dir Γ f g h = cohT Γ Comp₃T (λ P →
    A₁ P (var 2) (var 4) (var 6) >>= λ a → A₂ P (var 2) (var 4) (var 6) >>= λ a' →
    vcomp P (a ∷ a' ∷ []) >>= λ l →
    vcomp P (var 2 ∷ var 4 ∷ []) >>= λ fg → vcomp P (fg ∷ var 6 ∷ []) >>= λ fg-h →
    vcomp P (var 4 ∷ var 6 ∷ []) >>= λ gh → vcomp P (var 2 ∷ gh ∷ []) >>= λ f-gh →
    idc P (if inv then f-gh else fg-h) >>= λ r →
    just (if dir then (l , r) else (r , l)))
  (f ∷ g ∷ h ∷ [])
  where
  A₁ A₂ : Ctx → Tm → Tm → Tm → Maybe Tm
  A₁ = if inv then assoc⁻ else assoc
  A₂ = if inv then assoc else assoc⁻

-- id ; X ⇒ X  (left = true)  or  X ; id ⇒ X  (left = false), for an
-- n-cell X (n ≥ 1); dir = false gives the reverse.
unitor : Bool → Bool → Ctx → Tm → Maybe Tm
unitor isLeft dir Γ X = dimOf Γ X >>= λ n →
  cohT Γ (chain n) (λ P →
    let top = var (n + n) in
    srcOf P top >>= λ s → tgtOf P top >>= λ t →
    idc P (if isLeft then s else t) >>= λ i →
    vcomp P (if isLeft then (i ∷ top ∷ []) else (top ∷ i ∷ [])) >>= λ l →
    just (if dir then (l , top) else (top , l)))
  (X ∷ [])
