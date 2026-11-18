------------------------------------------------------------------------
-- Term builders for pure CaTT: unbiased composites over Batanin trees
-- and binary composites / whiskerings u ∗ₖ v of cells of any
-- dimensions. They are plain functions on raw syntax; every use is
-- validated by the certified checker (CaTTExp.Check), so nothing here
-- needs to be trusted.
------------------------------------------------------------------------
module CaTTExp.Free.Builders where

open import CaTTExp.Prelude
open import CaTTExp.Pure

-- A term together with its type.
TT : Set
TT = Tm × Ty

------------------------------------------------------------------------
-- List utilities.

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

dropL : ∀ {A : Set} → Nat → List A → List A
dropL zero    xs       = xs
dropL (suc n) []       = []
dropL (suc n) (_ ∷ xs) = dropL n xs

range : Nat → List Nat
range n = go n []
  where
  go : Nat → List Nat → List Nat
  go zero    acc = acc
  go (suc k) acc = go k (k ∷ acc)

------------------------------------------------------------------------
-- Iterated boundaries of a type, lowest dimension first:
-- bdry (s₁ →_{s₀ → t₀} t₁) = (s₀ , t₀) ∷ (s₁ , t₁) ∷ [].

bdry : Ty → List (Tm × Tm)
bdry ⋆           = []
bdry (arr A s t) = bdry A ++ ((s , t) ∷ [])

flat : List (Tm × Tm) → List Tm
flat []              = []
flat ((s , t) ∷ rest) = s ∷ t ∷ flat rest

------------------------------------------------------------------------
-- Trees.

disc : Nat → Tree
disc zero    = leaf
disc (suc n) = node (disc n ∷ [])

-- The pasting diagram Dᵖ ∨ₖ D^q (a p-disc and a q-disc glued along a
-- k-disc), for k < p and k < q.
wedge : Nat → Nat → Nat → Tree
wedge zero    (suc p) (suc q) = node (disc p ∷ disc q ∷ [])
wedge (suc k) (suc p) (suc q) = node (wedge k p q ∷ [])
wedge _       _       _       = leaf

mutual
  height : Tree → Nat
  height (node ts) = heights ts

  heights : List Tree → Nat
  heights []       = 0
  heights (t ∷ ts) = max (suc (height t)) (heights ts)

mutual
  truncate : Nat → Tree → Tree
  truncate zero    (node _)  = leaf
  truncate (suc n) (node ts) = node (truncates n ts)

  truncates : Nat → List Tree → List Tree
  truncates n []       = []
  truncates n (t ∷ ts) = truncate n t ∷ truncates n ts

isDisc : Tree → Bool
isDisc (node [])           = true
isDisc (node (t ∷ []))     = isDisc t
isDisc (node (_ ∷ _ ∷ _))  = false

lastTy : Ctx → Ty
lastTy ε       = ⋆
lastTy (_ ▸ A) = A

------------------------------------------------------------------------
-- The unbiased composite over a tree T, as a term of ctxOf T, with its
-- type (BMOSV Def. 2.1): a disc composes to its top variable; otherwise
-- coh_{T, comp ∂⁻T → comp ∂⁺T}.

compT : Nat → Tree → TT
compT zero       T = var 0 , ⋆
compT (suc fuel) T with height T | isDisc T
... | zero  | _     = var 0 , ⋆
... | suc h | true  = var (len (ctxOf T) ∸ 1) , lastTy (ctxOf T)
... | suc h | false =
  let Γ  = ctxOf T
      cA = compT fuel (truncate h T)
      s  = ⟪ map var (srcVars h Γ) ⟫
      t  = ⟪ map var (tgtVars h Γ) ⟫
      ty = arr (snd cA [ s ]ty) (fst cA [ s ]tm) (fst cA [ t ]tm)
  in coh Γ ty (idₛ Γ) , ty

-- The type of the composite, which is what a coh over T needs.
compTy : Tree → Ty
compTy T = snd (compT (suc (height T)) T)

------------------------------------------------------------------------
-- Binary composite u ∗ₖ v of a p-cell u and a q-cell v (k < p, q)
-- whose k-target and k-source agree. When p ≠ q this is a whiskering.
-- The substitution lists u's disc and then the part of v's disc not
-- shared with u, in the order of the pasting context.

_∗[_]_ : TT → Nat → TT → TT
(u , A) ∗[ k ] (v , B) =
  let W  = wedge k (dim A) (dim B)
      T  = compTy W
      bs = bdry B
      σ  = ⟪ flat (bdry A) ++ (u ∷ [])
            ++ (sndAt k bs ∷ flat (dropL (suc k) bs) ++ (v ∷ [])) ⟫
  in coh (ctxOf W) T σ , T [ σ ]ty
  where
  sndAt : Nat → List (Tm × Tm) → Tm
  sndAt _       []             = var 0
  sndAt zero    ((_ , t) ∷ _)  = t
  sndAt (suc n) (_ ∷ rest)     = sndAt n rest

infixl 6 _∗[_]_

-- Identity on a typed cell (coherence over its disc).
idc : TT → TT
idc (u , A) =
  let n  = dim A
      Dn = ctxOf (disc n)
      ty = arr (lastTy Dn) (var (len Dn ∸ 1)) (var (len Dn ∸ 1))
      σ  = ⟪ flat (bdry A) ++ (u ∷ []) ⟫
  in coh Dn ty σ , ty [ σ ]ty

-- A coherence over a pasting context given by a tree, between two
-- terms of that context, applied to a list of terms.
cohT : Tree → Ty → List Tm → TT
cohT T ty ts = coh (ctxOf T) ty ⟪ ts ⟫ , ty [ ⟪ ts ⟫ ]ty

-- Typecheck a typed term: succeeds only if the checker infers exactly
-- the claimed type.
checksM : (Γ : Ctx) (t : Tm) (A : Ty) → Maybe (Σ Ty (Γ ⊢tm t ∶_)) → Bool
checksM Γ t A nothing        = false
checksM Γ t A (just (B , _)) = A ==Ty B

checks : Ctx → TT → Bool
checks Γ (t , A) = checksM Γ t A (infer Γ t)

-- A certified derivation of Γ ⊢ t : A, produced by the checker at
-- typechecking time. It only typechecks if `checks Γ (t , A)` is true.
certify : (Γ : Ctx) (tA : TT) → {T (checks Γ tA)} → Γ ⊢tm fst tA ∶ snd tA
certify Γ (t , A) {p} = go (infer Γ t) p
  where
  go : (m : Maybe (Σ Ty (Γ ⊢tm t ∶_))) → T (checksM Γ t A m) → Γ ⊢tm t ∶ A
  go (just (B , d)) q = subst (Γ ⊢tm t ∶_) (sym (==Ty-sound A B q)) d

-- A certified derivation of Γ ⊢ctx.
certifyCtx : (Γ : Ctx) → {T (is-just (checkCtx Γ))} → Γ ⊢ctx
certifyCtx Γ {p} = from-just (checkCtx Γ) {p}
