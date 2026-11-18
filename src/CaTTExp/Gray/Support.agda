------------------------------------------------------------------------
-- The side condition of two-tier L (notes/pseudo-vs-gray.md §3).
--
-- A pasting context Γ = ΣΘ₁ ∨ … ∨ ΣΘₙ has objects a₀ … aₙ and one hom
-- Θₖ between aₖ₋₁ and aₖ. Its *Gray unfolding* is the Steiner complex
--
--     K(Γ)  =  λΘ₁ ⊗ … ⊗ λΘₙ          (factors in execution order)
--
-- whose basis elements are tuples (v₁, …, vₙ) of variables, vₖ a cell
-- of Θₖ, of dimension Σ (dim vₖ − 1). Tuples are lists of de Bruijn
-- levels of Γ; the empty tuple is the unit (a hom aᵢ → aᵢ).
--
-- Supports. Every term t over Γ is read in the free strict
-- Gray-enriched category on Γ, keeping only the set of basis elements
-- in the top chain of its image:
--
--   topS (var v)        = {(v)}
--   topS (coh Θ A ρ)    = F_ρ (top of the coh's cell in K(Θ))
--
-- where the coh's cell is the total cell T(Θ) = ⟨Θ₁⟩ ⊗ … ⊗ ⟨Θₙ⟩ in
-- the operation case and an identity (top chain 0) in the coherence
-- case, and F_ρ sends a tuple (w₁ … wₘ) to the concatenated products
-- topS(ρ w₁) × … × topS(ρ wₘ). All chains involved are non-negative
-- (top chains of T are sums of basis elements; images of non-negative
-- chains under F_ρ are non-negative), so supports of sums and tensor
-- products are unions and products of supports: no integer
-- arithmetic is needed. Composition across objects is concatenation
-- of tuples, because K(Γ)(aᵢ,aⱼ) ⊗ K(Γ)(aⱼ,aₖ) = K(Γ)(aᵢ,aₖ).
--
-- The support of t : A is that of t together with the supports of the
-- cells in A (type-directed, like Finster–Mimram's Var(t : A)):
--
--   supp(t : A) = topS t ∪ topS(s) ∪ topS(s') ∪ supp(type of s) …
--
-- Under soundness (Theorem 1 of the note) this is the union of the
-- chains of ⟦t⟧'s table. The side condition compares *downward
-- closures* ↓S in K(Γ) (close under replacing an entry of a tuple by
-- its source or target), as in §3.6 of the note. ↓S = ↓R is decided
-- on generators (`sameDown`: every element of S is below one of R and
-- vice versa), so no closure is built; `down` computes closures and
-- is kept for the rule-level checks of Gray.Bounded. The note: "the
-- downward-closed set of basis elements used by ⟦t⟧ and its boundaries". This is also
-- the form in which lemma (B) "support determines the cell" is known
-- (Hadzihasanovic: molecules are determined by their closed subsets).
--
-- Side condition for coh_{Γ, t →_A u}, with d = Σ dim Θₖ:
--   A = ⋆:   d = 0, t = a₀, u = aₙ                       (composites of
--                                                        1-cells, identity)
--   A ≠ ⋆:   the ⋆-endpoints of A are a₀ and aₙ, and either
--     (coherence) ↓supp(t:A) = ↓supp(u:A) = ↓Supp(T)   (all of K(Γ))
--     (operation) dim A = d, ↓supp(t:A) = ↓Supp(∂⁻T), ↓supp(u:A) = ↓Supp(∂⁺T)
--
-- T's table is the Steiner/Ara–Maltsiniotis tensor of the tables of the
-- ⟨Θₖ⟩:  (x⊗y)^ε_k = Σ_{i+j=k} x^ε_i ⊗ y^{(-1)^i ε}_j, with x_i^± = x_i
-- in x's top dimension. The ⟨Θ⟩ tables are those of a globular pasting
-- diagram: ⟨Θ⟩^-_i are the i-cells that are not the target of an
-- (i+1)-cell, ⟨Θ⟩^+_i those that are not a source.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Support (𝕊 : Signature) where

open Signature 𝕊

------------------------------------------------------------------------
-- List utilities.

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

-- 0, 1, …, n
upto : Nat → List Nat
upto zero    = 0 ∷ []
upto (suc n) = upto n ++ (suc n ∷ [])

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p []       = false
any p (x ∷ xs) = p x ∨ any p xs

sumL : List Nat → Nat
sumL []       = 0
sumL (n ∷ ns) = n + sumL ns

maxL : List Nat → Nat
maxL []       = 0
maxL (n ∷ ns) = max n (maxL ns)

odd : Nat → Bool
odd zero    = false
odd (suc n) = not (odd n)

------------------------------------------------------------------------
-- Tuples and finite sets of tuples.

Tuple : Set
Tuple = List Nat

TSet : Set
TSet = List Tuple

_==T_ : Tuple → Tuple → Bool
[]       ==T []       = true
(x ∷ xs) ==T (y ∷ ys) = (x ==ℕ y) ∧ (xs ==T ys)
_        ==T _        = false

memT : Tuple → TSet → Bool
memT x = any (x ==T_)

⊆T : TSet → TSet → Bool
⊆T xs ys = all (λ x → memT x ys) xs

≈T : TSet → TSet → Bool
≈T xs ys = ⊆T xs ys ∧ ⊆T ys xs

-- Elementwise product: { x ∷ y | x ∈ xs, y ∈ ys }.
prod1 : List Nat → TSet → TSet
prod1 xs ys = concatMap (λ x → map (x ∷_) ys) xs

-- { x ++ y | x ∈ xs, y ∈ ys }.
prodT : TSet → TSet → TSet
prodT xs ys = concatMap (λ x → map (x ++_) ys) xs

------------------------------------------------------------------------
-- The hom structure of a pasting context.

-- The ⋆-level endpoints of a type of dimension ≥ 1.
endsTy : Ty → Maybe (Tm × Tm)
endsTy ⋆                       = nothing
endsTy (arr ⋆ a b)             = just (a , b)
endsTy (arr (arr A s t) _ _)   = endsTy (arr A s t)

-- Context entries, left to right, with their levels.
entries : Ctx → List (Nat × Ty)
entries ε       = []
entries (Γ ▸ A) = entries Γ ++ ((len Γ , A) ∷ [])

isStar : Ty → Bool
isStar ⋆ = true
isStar _ = false

objs : Ctx → List Nat
objs Γ = map fst (filter (λ e → isStar (snd e)) (entries Γ))

-- Position of an element in a list.
posOf : Nat → List Nat → Maybe Nat
posOf n []       = nothing
posOf n (m ∷ ms) = if n ==ℕ m then just 0 else (posOf n ms >>= λ k → just (suc k))

-- A cell of some hom: its level, its hom index k (it lives in Θₖ,
-- k ≥ 1), its dimension inside the hom, and its source and target
-- (levels) when that dimension is ≥ 1.
record El : Set where
  constructor el
  field
    lvl  : Nat
    hom  : Nat
    hdim : Nat
    src  : Nat
    tgt  : Nat
open El public

private
  varLvl : Tm → Maybe Nat
  varLvl (var i) = just i
  varLvl _       = nothing

  bdry : Ty → Nat × Nat
  bdry (arr (arr _ _ _) (var s) (var t)) = s , t
  bdry _                                 = 0 , 0

  mkEl : List Nat → Nat × Ty → List El
  mkEl os (v , A) with endsTy A
  ... | nothing      = []
  ... | just (_ , b) with varLvl b
  ...   | nothing = []
  ...   | just b' with posOf b' os
  ...     | nothing = []
  ...     | just k  = el v k (dim A ∸ 1) (fst (bdry A)) (snd (bdry A)) ∷ []

cells : Ctx → List El
cells Γ = concatMap (mkEl (objs Γ)) (entries Γ)

-- One hom Θₖ: its dimension and its cells.
record Hom : Set where
  constructor mkHom
  field
    hd  : Nat
    hcs : List El
open Hom public

homs : Ctx → List Hom
homs Γ = map one (drop1 (upto (lengthN (objs Γ))))
  where
  lengthN : List Nat → Nat
  lengthN []       = 0
  lengthN (_ ∷ xs) = suc (lengthN xs)
  -- hom indices 1 … n (n + 1 objects); upto gives 0 … n+1.
  drop1 : List Nat → List Nat
  drop1 []       = []
  drop1 (_ ∷ xs) = dropLast xs
    where
    dropLast : List Nat → List Nat
    dropLast []           = []
    dropLast (x ∷ [])     = []
    dropLast (x ∷ y ∷ ys) = x ∷ dropLast (y ∷ ys)
  one : Nat → Hom
  one k = let cs = filter (λ c → hom c ==ℕ k) (cells Γ) in mkHom (maxL (map hdim cs)) cs

-- d = Σ dim Θₖ, the dimension of K(Γ).
dimK : List Hom → Nat
dimK hs = sumL (map hd hs)

------------------------------------------------------------------------
-- Tables of the ⟨Θₖ⟩ and of their tensor T.

-- ⟨Θ⟩^sg_i as a set of levels (sg = true is +, false is −).
piece : Hom → Nat → Bool → List Nat
piece h i sg =
  if i ==ℕ hd h then map lvl (filter (λ c → hdim c ==ℕ i) (hcs h))
  else if i <ℕ hd h then
    map lvl (filter (λ c → (hdim c ==ℕ i) ∧ not (any (hits c) (hcs h))) (hcs h))
  else []
  where
  -- c ∉ ⟨Θ⟩^-_i iff c is the target of some (i+1)-cell, and
  -- c ∉ ⟨Θ⟩^+_i iff c is the source of some (i+1)-cell.
  hits : El → El → Bool
  hits c w = (hdim w ==ℕ suc i) ∧ (if sg then (src w ==ℕ lvl c) else (tgt w ==ℕ lvl c))

-- T^sg_k.
chainT : Bool → Nat → List Hom → TSet
chainT sg k []       = if k ==ℕ 0 then [] ∷ [] else []
chainT sg k (h ∷ hs) =
  concatMap (λ i → prod1 (piece h i sg) (chainT (if odd i then not sg else sg) (k ∸ i) hs))
            (filter (λ i → i <ℕ suc k) (upto k))

-- Union of T^±_k for k < m.
lowerT : Nat → List Hom → TSet
lowerT zero    hs = []
lowerT (suc m) hs = lowerT m hs ++ chainT false m hs ++ chainT true m hs

topT : List Hom → TSet
topT hs = chainT true (dimK hs) hs

-- Supp(T), Supp(∂⁻T), Supp(∂⁺T).
fullT : List Hom → TSet
fullT hs = lowerT (dimK hs) hs ++ topT hs

bdryT : Bool → List Hom → TSet
bdryT sg hs = lowerT (dimK hs ∸ 1) hs ++ chainT sg (dimK hs ∸ 1) hs

------------------------------------------------------------------------
-- Supports of terms.

-- Downward closure in K(Γ).

findEl : Nat → List El → Maybe El
findEl n []       = nothing
findEl n (c ∷ cs) = if lvl c ==ℕ n then just c else findEl n cs

-- Boundary elements of one entry (none for a cell of dimension 0).
bdEl : List El → Nat → List Nat
bdEl cs w with findEl w cs
... | nothing = []
... | just c  = if hdim c ==ℕ 0 then [] else (src c ∷ tgt c ∷ [])

private
  -- Codimension-1 faces of a tuple.
  faces : List El → Tuple → TSet
  faces cs []       = []
  faces cs (w ∷ ws) = map (_∷ ws) (bdEl cs w) ++ map (w ∷_) (faces cs ws)

  nubT : TSet → TSet
  nubT []       = []
  nubT (x ∷ xs) = if memT x xs then nubT xs else (x ∷ nubT xs)

  closeN : Nat → List El → TSet → TSet
  closeN zero    cs S = S
  closeN (suc n) cs S = closeN n cs (nubT (S ++ concatMap (faces cs) S))

down : Ctx → TSet → TSet
down Γ S = closeN (dimK (homs Γ)) (cells Γ) (nubT S)

-- The face order on entries: a ≤ b if a is reached from b by at most
-- n source/target steps. Tuples are compared entrywise.
leqL : List El → Nat → Nat → Nat → Bool
leqL cs zero    a b = a ==ℕ b
leqL cs (suc n) a b = (a ==ℕ b) ∨ anyB (bdEl cs b)
  where
  anyB : List Nat → Bool
  anyB []       = false
  anyB (c ∷ bs) = leqL cs n a c ∨ anyB bs

leqT : List El → Nat → Tuple → Tuple → Bool
leqT cs n []       []       = true
leqT cs n (a ∷ x)  (b ∷ y)  = leqL cs n a b ∧ leqT cs n x y
leqT cs n _        _        = false

-- ↓S ⊆ ↓R, decided on generators: every s ∈ S is below some r ∈ R.
covers : Ctx → TSet → TSet → Bool
covers Γ S R =
  all (λ s → any (leqT (cells Γ) (dimK (homs Γ)) s) R) S

-- ↓S = ↓R.
sameDown : Ctx → TSet → TSet → Bool
sameDown Γ S R = covers Γ S R ∧ covers Γ R S

nth : Nat → List TSet → TSet
nth _       []       = []
nth zero    (x ∷ _)  = x
nth (suc n) (_ ∷ xs) = nth n xs

-- F_ρ on one tuple, given the top supports of ρ's terms (by level).
Ftuple : List TSet → Tuple → TSet
Ftuple tops []       = [] ∷ []
Ftuple tops (w ∷ ws) = prodT (nth w tops) (Ftuple tops ws)

applyF : List TSet → TSet → TSet
applyF tops C = concatMap (Ftuple tops) C

isVarAt : Tm → Nat → Bool
isVarAt (var i) n = i ==ℕ n
isVarAt _       _ = false

-- The first and last objects.
private
  firstL lastL : List Nat → Nat
  firstL []       = 0
  firstL (x ∷ _)  = x
  lastL []           = 0
  lastL (x ∷ [])     = x
  lastL (_ ∷ y ∷ ys) = lastL (y ∷ ys)

-- The ⋆-endpoints of A are a₀ and aₙ.
endsOK : Ctx → Ty → Bool
endsOK Γ A with endsTy A
... | nothing      = false
... | just (s , t) = isVarAt s (firstL (objs Γ)) ∧ isVarAt t (lastL (objs Γ))

mutual
  topS : Tm → TSet
  topS (var v)              = (v ∷ []) ∷ []
  topS (cst _)              = []
  topS (coh Θ ⋆ ρ)          = []
  topS (coh Θ (arr A t u) ρ) =
    applyF (topsSub ρ) (if cohCase Θ A t u then [] else topT (homs Θ))

  topsSub : Sub → List TSet
  topsSub ⟨⟩       = []
  topsSub (ρ ,ₛ t) = topsSub ρ ++ (topS t ∷ [])

  -- Supports of the cells in a type (objects contribute nothing).
  suppTy : Ty → TSet
  suppTy ⋆                     = []
  suppTy (arr ⋆ _ _)           = []
  suppTy (arr (arr B s s') t u) = suppTy (arr B s s') ++ topS t ++ topS u

  supp : Tm → Ty → TSet
  supp t A = topS t ++ suppTy A

  -- The coherence case (only for A ≠ ⋆).
  cohCase : Ctx → Ty → Tm → Tm → Bool
  cohCase Θ ⋆ t u = false
  cohCase Θ A@(arr _ _ _) t u =
    endsOK Θ A ∧ sameDown Θ (supp t A) (fullT (homs Θ))
               ∧ sameDown Θ (supp u A) (fullT (homs Θ))

-- The operation case.
opCase : Ctx → Ty → Tm → Tm → Bool
opCase Θ ⋆ t u =
  (dimK (homs Θ) ==ℕ 0) ∧ isVarAt t (firstL (objs Θ)) ∧ isVarAt u (lastL (objs Θ))
opCase Θ A@(arr _ _ _) t u =
  endsOK Θ A ∧ (dim A ==ℕ dimK (homs Θ))
  ∧ sameDown Θ (supp t A) (bdryT false (homs Θ))
  ∧ sameDown Θ (supp u A) (bdryT true (homs Θ))

-- The side condition of two-tier L.
graySide : Ctx → Ty → Tm → Tm → Bool
graySide Θ A t u = cohCase Θ A t u ∨ opCase Θ A t u
