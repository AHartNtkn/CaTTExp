------------------------------------------------------------------------
-- Certified results about the Gray-context constructions.
--
-- Every theorem here is obtained by running the certified checker of
-- CaTTExp.Check at typechecking time; a success carries a typing
-- derivation, which is what the theorems return. The constructions
-- themselves (Cylinder, VComp, Cube) are untrusted meta-programs.
--
-- What is and is not proved is summarised in notes/gray-cylinders.md.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Checks.Base where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.VComp
open import CaTTExp.GrayCtx.Cube

------------------------------------------------------------------------
-- Certificates.

-- A construction that produced a well-formed context.
WF : Maybe Ctx → Set
WF m = Σ Ctx λ Γ → (m ≡ just Γ) × (Γ ⊢ctx)

-- A construction that produced a context Γ and a substitution Γ ⊢ σ : Δ.
WFSub : Maybe (Ctx × Sub) → Ctx → Set
WFSub m Δ = Σ Ctx λ Γ → Σ Sub λ σ → (m ≡ just (Γ , σ)) × (Γ ⊢ctx) × (Γ ⊢sub σ ∶ Δ)

wf? : (m : Maybe Ctx) → Maybe (WF m)
wf? nothing  = nothing
wf? (just Γ) = (λ d → Γ , refl , d) <$> checkCtx Γ

wfSub? : (m : Maybe (Ctx × Sub)) (Δ : Ctx) → Maybe (WFSub m Δ)
wfSub? nothing        Δ = nothing
wfSub? (just (Γ , σ)) Δ =
  checkCtx Γ >>= λ w → checkSub Γ w σ Δ >>= λ s → just (Γ , σ , refl , w , s)

-- Extracting a certificate from a successful run.
cert : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
cert (just x) _ = x

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

all-∈ : ∀ {A : Set} (p : A → Bool) {x} xs → T (all p xs) → x ∈ xs → T (p x)
all-∈ p (y ∷ ys) h here      = ∧-fst {p y} h
all-∈ p (y ∷ ys) h (there m) = all-∈ p ys (∧-snd {p y} h) m

------------------------------------------------------------------------
-- Named contexts and the enumeration of small pasting schemes.

D : Nat → Ctx
D n = ctxOf (chain n)

-- x —f→ y —g→ z;  α : f ⇒ g, β : g ⇒ h;  α, β horizontally composable
Comp₂ VComp HComp : Ctx
Comp₂ = ctxOf (node (leaf ∷ leaf ∷ []))
VComp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))
HComp = ctxOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []))

private
  concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
  concatMap f []       = []
  concatMap f (x ∷ xs) = f x ++ concatMap f xs

-- Plane forests with exactly n edges (fuel f ≥ n + 1).
forests : Nat → Nat → List (List Tree)
forests zero    _       = []
forests (suc f) zero    = [] ∷ []
forests (suc f) (suc n) =
  concatMap (λ k → concatMap (λ ch → mapL (λ rest → node ch ∷ rest) (forests f (n ∸ k)))
                             (forests f k))
            (upto (suc n))

trees≤ : Nat → List Tree
trees≤ n = concatMap (λ k → mapL node (forests (suc k) k)) (upto (suc n))

-- Sanity check on the enumeration: 1 + 1 + 2 + 5 + 14 (Catalan).
_ : length (trees≤ 4) ≡ 23
_ = refl

