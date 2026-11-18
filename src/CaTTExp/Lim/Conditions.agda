------------------------------------------------------------------------
-- The side conditions of CaTT_lim (Mikhail, arXiv 2412.13310v2).
--
--  * Linearity x ∝ t (Def. 3.1).
--  * The selector  ⋃ { FV(p : T_p) | p ∈ Π, y ∈ FV(δ(x) : ∂X), y ∝ τ(p) }.
--  * δCond(t : A, x : X, Π): x ∝ t and
--        FV(t : A) = FV(x : X) ∪ selector            (Def. 4.15)
--  * τCond‾(t : A, x : X, c : Ob, Π):
--        FV(t : A) = {c} ∪ selector                   (Def. 4.15)
--
-- "t : A is categorical" (built from CaTT rules only) holds for every
-- term of pure CaTT; it is enforced by the typing premise of each rule.
--
-- The selector is parameterised by which boundary of p is tested
-- (`via`). The printed rules always test τ(p); the repair of the
-- gray/ctrf source condition tests σ(p) instead (Repaired.agda).
------------------------------------------------------------------------
module CaTTExp.Lim.Conditions where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named

data Side : Set where
  σ τ : Side

------------------------------------------------------------------------
-- Dimensions.

dimOf : NCtx → Name → Nat
dimOf K n with typeOf K n
... | just A  = dim A
... | nothing = 0

dimTm : NCtx → Tm → Nat
dimTm K (var n)     = dimOf K n
dimTm K (coh _ A _) = dim A
dimTm K (cst ())

------------------------------------------------------------------------
-- Linearity (Def. 3.1). `lin K x d t` decides x ∝ t where d = dim x;
-- the relation is only defined when dim t = d, which is checked at the
-- top (`linear`) and, for arguments γᵢ of a coh, through the dimension
-- of the corresponding variable of the coh's pasting context.

mutual
  lin : NCtx → Name → Nat → Tm → Bool
  lin K x d (var y)     = x ==ℕ y
  lin K x d (coh Δ A γ) = countLin K x d Δ γ ==ℕ 1
  lin K x d (cst ())

  -- Number of arguments γᵢ of dimension d with x ∝ γᵢ.
  countLin : NCtx → Name → Nat → Ctx → Sub → Nat
  countLin K x d (Δ ▸ B) (γ ,ₛ t) =
    (if (dim B ==ℕ d) ∧ lin K x d t then 1 else 0) + countLin K x d Δ γ
  countLin K x d _ _ = 0

linearP : NCtx → Name → Tm → Bool
linearP K x t = (dimOf K x ==ℕ dimTm K t) ∧ lin K x (dimOf K x) t

------------------------------------------------------------------------
-- Strict linearity (repair of open issue D3b). The printed OP case only
-- asks that exactly one argument be linear in x; x may still occur in
-- other arguments. E.g. for a loop ℓ, ℓ ∝ (ℓ·ℓ)·ℓ holds, since only the
-- right argument is linear in ℓ. The strict test also asks that x occur
-- in exactly one argument (multiplicity one).

mutual
  lin₁ : NCtx → Name → Nat → Tm → Bool
  lin₁ K x d (var y)     = x ==ℕ y
  lin₁ K x d (coh Δ A γ) = (countLin₁ K x d Δ γ ==ℕ 1) ∧ (countOcc x γ ==ℕ 1)
  lin₁ K x d (cst ())

  countLin₁ : NCtx → Name → Nat → Ctx → Sub → Nat
  countLin₁ K x d (Δ ▸ B) (γ ,ₛ t) =
    (if (dim B ==ℕ d) ∧ lin₁ K x d t then 1 else 0) + countLin₁ K x d Δ γ
  countLin₁ K x d _ _ = 0

  -- Number of arguments in which x occurs at all.
  countOcc : Name → Sub → Nat
  countOcc x ⟨⟩       = 0
  countOcc x (γ ,ₛ t) = (if elem x (fvTm t) then 1 else 0) + countOcc x γ

linear₁ : NCtx → Name → Tm → Bool
linear₁ K x t = (dimOf K x ==ℕ dimTm K t) ∧ lin₁ K x (dimOf K x) t

-- Which linearity test the rules use.
data Lin : Set where
  printedLin strictLin : Lin

linearBy : Lin → NCtx → Name → Tm → Bool
linearBy printedLin = linearP
linearBy strictLin  = linear₁

-- The printed test (Def. 3.1).
linear : NCtx → Name → Tm → Bool
linear = linearBy printedLin

------------------------------------------------------------------------
-- Boundaries.

bdry : Side → Ty → Maybe Tm
bdry σ (arr _ s _) = just s
bdry τ (arr _ _ t) = just t
bdry _ ⋆           = nothing

-- FV(δ(x) : ∂X), empty when X = ⋆ (δ(x) undefined).
fvBdry : Side → Ty → List Name
fvBdry δ ⋆                   = []
fvBdry σ (arr B s _)         = fvTmTy s B
fvBdry τ (arr B _ t)         = fvTmTy t B

-- FV(x : X) for a name.
fvVar : NCtx → Name → List Name
fvVar K x with typeOf K x
... | just X  = x ∷ fvTy X
... | nothing = x ∷ []

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p []       = false
any p (x ∷ xs) = p x ∨ any p xs

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

-- Does some y ∈ Y satisfy y ∝ via(p)?
selectsBy : Lin → NCtx → Side → List Name → Name → Bool
selectsBy lm K via Y p with typeOf K p
... | nothing = false
... | just T  with bdry via T
...   | nothing = false
...   | just u  = any (λ y → linearBy lm K y u) Y

-- ⋃ { FV(p : T_p) | p ∈ Π, y ∈ Y, y ∝ via(p) }
selectorBy : Lin → NCtx → Side → List Name → List Name → List Name
selectorBy lm K via Y Π = concatMap (λ p → if selectsBy lm K via Y p then fvVar K p else []) Π

selector : NCtx → Side → List Name → List Name → List Name
selector = selectorBy printedLin

------------------------------------------------------------------------
-- The conditions, evaluated in the context K in which s →_A t is formed.

-- δCond(t : A, x : X, Π) with the selector testing `via`.
condBy : Lin → NCtx → (δ via : Side) → Tm → Ty → Name → List Name → Bool
condBy lm K δ via t A x Π with typeOf K x
... | nothing = false
... | just X  = linearBy lm K x t ∧
               ≈? (fvTmTy t A) (fvVar K x ++ selectorBy lm K via (fvBdry δ X) Π)

cond : NCtx → (δ via : Side) → Tm → Ty → Name → List Name → Bool
cond = condBy printedLin

-- δCond‾(t : A, x : X, c : Ob, Π): no linearity, FV(x : X) replaced by {c}.
condBarBy : Lin → NCtx → (δ : Side) → Tm → Ty → Name → Name → List Name → Bool
condBarBy lm K δ t A x c Π with typeOf K x
... | nothing = false
... | just X  = ≈? (fvTmTy t A) (c ∷ selectorBy lm K τ (fvBdry δ X) Π)

condBar : NCtx → (δ : Side) → Tm → Ty → Name → Name → List Name → Bool
condBar = condBarBy printedLin

------------------------------------------------------------------------
-- Facts used to refute side conditions with an abstract term.

elem-++ˡ : ∀ a xs ys → T (elem a xs) → T (elem a (xs ++ ys))
elem-++ˡ a (x ∷ xs) ys p with a ==ℕ x
... | true  = tt
... | false = elem-++ˡ a xs ys p

elem-++ʳ : ∀ a xs ys → T (elem a ys) → T (elem a (xs ++ ys))
elem-++ʳ a []       ys p = p
elem-++ʳ a (x ∷ xs) ys p with a ==ℕ x
... | true  = tt
... | false = elem-++ʳ a xs ys p

⊆?-elem : ∀ a xs ys → T (⊆? xs ys) → T (elem a xs) → T (elem a ys)
⊆?-elem a (x ∷ xs) ys p q with elem x ys in ex | a ==ℕ x in ax
... | true  | true  = subst (λ b → T (elem b ys)) (sym (==ℕ-sound a x (subst T (sym ax) tt)))
                        (subst T (sym ex) tt)
... | true  | false = ⊆?-elem a xs ys p q
⊆?-elem a (x ∷ xs) ys () q | false | _

-- If FV(t : A) is required to equal R, and some name a of t : A is
-- not in R, the condition fails, whatever t is.
blocked : ∀ a xs R → T (elem a xs) → (T (elem a R) → ⊥) → T (≈? xs R) → ⊥
blocked a xs R inx notR p = notR (⊆?-elem a xs R (∧-fst {⊆? xs R} p) inx)
