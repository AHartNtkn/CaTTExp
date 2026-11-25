------------------------------------------------------------------------
-- The strips of the descent (ledger S20 (i), stage 4c; notes/
-- rc-generator.md §1, stage 4 plan; tools/rc_descent.py strip_right).
--
-- All terms are typed terms (RCProc.TypedSub.TTm); composites are
-- built by the decided composition of RCProc.TypedOps, glue cells by
-- RCProc.GlueP (answered over their pasting context by rcP), and the
-- comparisons that need the descent itself (an inverse, a cancellation)
-- by a recursion oracle `rec` whose answers are typed terms.  So every
-- `just` is a typed term of Γ, whatever `rec` returns and whatever code
-- chose the pieces.
--
--   comp2?   : the composite along cut k of two typed cells (one of
--              them (k+1)-dimensional: a whisker or a composite)
--   idT      : the identity cell on a typed cell (rcP's identity case)
--   gcoh     : a glue cell over the chain pasting context of `cells`
--              along cut k (tools/rc_descent.py `_gcoh`)
--   unitT    : x ⇛ x ;ₖ 1 (or back)
--   stripR   : from V : t ;ₘ K ⇛ u ;ₘ K (m = n − 1) to t ⇛ u:
--              t ⇛ t1 ⇛ t(KK⁻) ⇛ (tK)K⁻ ⇛ (uK)K⁻ ⇛ u(KK⁻) ⇛ u1 ⇛ u
------------------------------------------------------------------------
module CaTTExp.RCProc.Strip where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc using (rcP)
open import CaTTExp.RCProc.Glue using (Ans)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (rcomp?; lcomp?; ansT)
open import CaTTExp.RCProc.GlueP using (glueT; varT; bdT; transT?)

-- A recursion oracle: an answer a ⇛ b for typed parallel a, b.
Rec : Ctx → Set
Rec Γ = TTm Γ → TTm Γ → Maybe (TTm Γ)

dimT : ∀ {Γ} → TTm Γ → Nat
dimT x = dim (ty x)

comp2? : ∀ {Γ} (k : Nat) → TTm Γ → TTm Γ → Maybe (TTm Γ)
comp2? k a b =
  if dimT b ==ℕ suc k then rcomp? k (dimT a ∸ suc k) a b
  else if dimT a ==ℕ suc k then lcomp? k (dimT b ∸ suc k) a b
  else nothing

idT : ∀ {Γ} → TTm Γ → Maybe (TTm Γ)
idT x = rcP (der x) (der x) >>= λ r → just (ansT r)

srcT tgtT : ∀ {Γ} → TTm Γ → Maybe (TTm Γ)
srcT x = bdT x >>= λ p → just (fst p)
tgtT x = bdT x >>= λ p → just (snd p)

private
  iter : ∀ {Γ} → Nat → (TTm Γ → Maybe (TTm Γ)) → TTm Γ → Maybe (TTm Γ)
  iter zero    f x = just x
  iter (suc n) f x = f x >>= iter n f

  disc : Nat → Tree
  disc zero    = leaf
  disc (suc n) = node (disc n ∷ [])

  wrap : Nat → Tree → Tree
  wrap zero    t = t
  wrap (suc k) t = node (wrap k t ∷ [])

  -- Maximal variables of a context, in level order (untrusted).
  maxVars : Ctx → List Nat
  maxVars P = filt 0 (len P)
    where
    used : Nat → Bool
    used i = go P
      where
      go : Ctx → Bool
      go ε = false
      go (Q ▸ ⋆) = go Q
      go (Q ▸ arr _ (var a) (var b)) = (a ==ℕ i) ∨ (b ==ℕ i) ∨ go Q
      go (Q ▸ arr _ _ _) = go Q
    filt : Nat → Nat → List Nat
    filt i zero    = []
    filt i (suc n) = if used i then filt (suc i) n else (i ∷ filt (suc i) n)

  zipL : ∀ {a b} {X : Set a} {Y : Set b} → List X → List Y → List (X × Y)
  zipL (x ∷ xs) (y ∷ ys) = (x , y) ∷ zipL xs ys
  zipL _ _ = []

  mapM : ∀ {a b} {X : Set a} {Y : Set b} → (X → Maybe Y) → List X → Maybe (List Y)
  mapM f []       = just []
  mapM f (x ∷ xs) = f x >>= λ y → mapM f xs >>= λ ys → just (y ∷ ys)

chainTree : Nat → List Nat → Tree
chainTree k dims = wrap k (node (mapL (λ d → disc (d ∸ suc k)) dims))
  where
  mapL : ∀ {a b} {X : Set a} {Y : Set b} → (X → Y) → List X → List Y
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

-- The glue cell lhs ⇛ rhs over the chain context of `cells` along cut
-- k; lhs, rhs are given the typed maximal variables of P.
gcoh : ∀ {Γ} → Γ ⊢ctx → (k : Nat) → (cells : List (TTm Γ)) →
       (∀ {Δ} → List (TTm Δ) → Maybe (TTm Δ)) →
       (∀ {Δ} → List (TTm Δ) → Maybe (TTm Δ)) → Maybe (TTm Γ)
gcoh w k cells lhs rhs =
  glueT w Tc (zipL mx cells) λ v →
    mapM v mx >>= λ xs → lhs xs >>= λ a → rhs xs >>= λ b → just (a , b)
  where
  Tc = chainTree k (mapD cells)
    where
    mapD : ∀ {Γ} → List (TTm Γ) → List Nat
    mapD []       = []
    mapD (x ∷ xs) = dimT x ∷ mapD xs
  mx = maxVars (ctxOf Tc)

-- x ⇛ x ;ₖ 1 (1 the identity on the k-target of x, raised to dimension
-- k + 1), or back.
unitT : ∀ {Γ} → Γ ⊢ctx → (k : Nat) → Bool → TTm Γ → Maybe (TTm Γ)
unitT w k back x = gcoh w 0 (x ∷ []) (if back then one else plain) (if back then plain else one)
  where
  plain one : ∀ {Δ} → List (TTm Δ) → Maybe (TTm Δ)
  plain (y ∷ _) = just y
  plain []      = nothing
  one (y ∷ _) = iter (dimT y ∸ k) tgtT y >>= idT >>= comp2? k y
  one []      = nothing

vchain : ∀ {Γ} → List (Maybe (TTm Γ)) → Maybe (TTm Γ)
vchain []       = nothing
vchain (c ∷ cs) = c >>= go cs
  where
  go : ∀ {Γ} → List (Maybe (TTm Γ)) → TTm Γ → Maybe (TTm Γ)
  go []       x = just x
  go (d ∷ ds) x = d >>= λ y → transT? x y >>= go ds

-- From V : t ;ₘ K ⇛ u ;ₘ K, with m = n − 1 and K an n-cell, to t ⇛ u.
stripR : ∀ {Γ} → Γ ⊢ctx → Rec Γ → (t u K V : TTm Γ) → Maybe (TTm Γ)
stripR w rec t u K V =
  srcT K >>= λ s → tgtT K >>= λ z →
  rec z s >>= λ Ki →
  comp2? m K Ki >>= λ KKi →
  idT s >>= λ one →
  rec one KKi >>= λ kapi →
  rec KKi one >>= λ kap →
  vchain (unitT w m false t
        ∷ comp2? m t kapi
        ∷ assoc t Ki false
        ∷ comp2? m V Ki
        ∷ assoc u Ki true
        ∷ comp2? m u kap
        ∷ unitT w m true u ∷ [])
  where
  m = dimT t ∸ 1
  la ra : ∀ {Δ} → List (TTm Δ) → Maybe (TTm Δ)
  la (x ∷ a ∷ b ∷ _) = comp2? m a b >>= comp2? m x
  la _ = nothing
  ra (x ∷ a ∷ b ∷ _) = comp2? m x a >>= λ xa → comp2? m xa b
  ra _ = nothing
  -- x(KK⁻) ⇛ (xK)K⁻, or back
  assoc : TTm _ → TTm _ → Bool → Maybe (TTm _)
  assoc x Ki back = gcoh w m (x ∷ K ∷ Ki ∷ []) (if back then ra else la) (if back then la else ra)
