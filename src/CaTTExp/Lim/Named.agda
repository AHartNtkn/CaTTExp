------------------------------------------------------------------------
-- Named contexts over pure CaTT.
--
-- Mikhail's CaTT_lim rules (arXiv 2412.13310, Def. 4.15) grow contexts
-- in the *middle*: a cone K = Γ, c, Π gets a new diagram variable
-- appended to Γ, and a conical transfor M₁; M₂; M₃ gets variables
-- appended to each block. With de Bruijn levels that would shift every
-- later variable. We therefore state these rules over contexts whose
-- variables carry names (natural numbers), exactly as the paper writes
-- them, and type-check by translating to the level-based core.
--
-- A named context is well formed (WfCtx) when its names are distinct,
-- every type mentions only earlier names, and its translation is a
-- well-formed context of the core (CaTTExp.Typing over the empty
-- signature). Terms are ordinary core terms in which `var n` refers to
-- the variable *named* n; the bodies of `coh` are closed core syntax,
-- so only their argument substitutions are renamed.
------------------------------------------------------------------------
module CaTTExp.Lim.Named where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)

Name : Set
Name = Nat

infixl 5 _▹_∶_

data NCtx : Set where
  ∅     : NCtx
  _▹_∶_ : NCtx → Name → Ty → NCtx

infixr 5 _⧺_
-- Append (the right context comes after the left one).
_⧺_ : NCtx → NCtx → NCtx
K ⧺ ∅           = K
K ⧺ (L ▹ x ∶ A) = (K ⧺ L) ▹ x ∶ A

names : NCtx → List Name
names ∅           = []
names (K ▹ x ∶ _) = names K ++ (x ∷ [])

size : NCtx → Nat
size ∅           = 0
size (K ▹ _ ∶ _) = suc (size K)

-- The type of a name (the last binding wins; well-formed contexts have
-- distinct names anyway).
typeOf : NCtx → Name → Maybe Ty
typeOf ∅           n = nothing
typeOf (K ▹ x ∶ A) n = if n ==ℕ x then just A else typeOf K n

-- The level of a name.
levelOf : NCtx → Name → Maybe Nat
levelOf ∅           n = nothing
levelOf (K ▹ x ∶ _) n = if n ==ℕ x then just (size K) else levelOf K n

-- The last variable of a context.
lastOf : NCtx → Maybe (Name × Ty)
lastOf ∅           = nothing
lastOf (K ▹ x ∶ A) = just (x , A)

------------------------------------------------------------------------
-- Renaming of free names (outside coh bodies), possibly failing.

mutual
  renTy : (Name → Maybe Nat) → Ty → Maybe Ty
  renTy ρ ⋆           = just ⋆
  renTy ρ (arr A t u) = renTy ρ A >>= λ A' → renTm ρ t >>= λ t' →
                        renTm ρ u >>= λ u' → just (arr A' t' u')

  renTm : (Name → Maybe Nat) → Tm → Maybe Tm
  renTm ρ (var n)     = ρ n >>= λ i → just (var i)
  renTm ρ (coh Δ A γ) = renSub ρ γ >>= λ γ' → just (coh Δ A γ')
  renTm ρ (cst ())

  renSub : (Name → Maybe Nat) → Sub → Maybe Sub
  renSub ρ ⟨⟩       = just ⟨⟩
  renSub ρ (γ ,ₛ t) = renSub ρ γ >>= λ γ' → renTm ρ t >>= λ t' → just (γ' ,ₛ t')

-- Total renaming name → name (used for copying a block of variables).
mutual
  rnTy : (Name → Name) → Ty → Ty
  rnTy ρ ⋆           = ⋆
  rnTy ρ (arr A t u) = arr (rnTy ρ A) (rnTm ρ t) (rnTm ρ u)

  rnTm : (Name → Name) → Tm → Tm
  rnTm ρ (var n)     = var (ρ n)
  rnTm ρ (coh Δ A γ) = coh Δ A (rnSub ρ γ)
  rnTm ρ (cst ())

  rnSub : (Name → Name) → Sub → Sub
  rnSub ρ ⟨⟩       = ⟨⟩
  rnSub ρ (γ ,ₛ t) = rnSub ρ γ ,ₛ rnTm ρ t

------------------------------------------------------------------------
-- Translation to the level-based core.

lower : NCtx → Maybe Ctx
lower ∅           = just ε
lower (K ▹ x ∶ A) =
  guard (not (elem x (names K))) λ _ →
  lower K >>= λ L → renTy (levelOf K) A >>= λ A' → just (L ▸ A')

-- A well-formed named context. A record (not a Σ) so that Agda can
-- infer K from the expected type.
record WfCtx (K : NCtx) : Set where
  constructor wf
  field
    core    : Ctx
    lowers  : lower K ≡ just core
    derived : core ⊢ctx

wf? : (K : NCtx) → Maybe (WfCtx K)
wf? K = go (lower K) refl
  where
  go : (m : Maybe Ctx) → lower K ≡ m → Maybe (WfCtx K)
  go nothing  _  = nothing
  go (just L) eq = checkCtx L >>= λ d → just (wf L eq d)

------------------------------------------------------------------------
-- Substitutions between named contexts. A substitution into M is a
-- core `Sub` listing one named term (over Ω) per variable of M, in M's
-- order. It is well typed when its translation is a core substitution
-- between the translated contexts.

record SubOK (Ω : NCtx) (θ : Sub) (M : NCtx) : Set where
  constructor subok
  field
    coreΩ    : Ctx
    coreM    : Ctx
    coreθ    : Sub
    lowersΩ  : lower Ω ≡ just coreΩ
    lowersM  : lower M ≡ just coreM
    lowersθ  : renSub (levelOf Ω) θ ≡ just coreθ
    wfΩ      : coreΩ ⊢ctx
    derived  : coreΩ ⊢sub coreθ ∶ coreM

sub? : (Ω : NCtx) (θ : Sub) (M : NCtx) → Maybe (SubOK Ω θ M)
sub? Ω θ M = go (lower Ω) refl (lower M) refl (renSub (levelOf Ω) θ) refl
  where
  go : (a : Maybe Ctx) → lower Ω ≡ a → (b : Maybe Ctx) → lower M ≡ b →
       (c : Maybe Sub) → renSub (levelOf Ω) θ ≡ c → Maybe (SubOK Ω θ M)
  go (just LΩ) e₁ (just LM) e₂ (just σ) e₃ =
    checkCtx LΩ >>= λ w → checkSub LΩ w σ LM >>= λ d →
    just (subok LΩ LM σ e₁ e₂ e₃ w d)
  go _ _ _ _ _ _ = nothing

-- Look up the term a substitution assigns to a name of M.
termFor : NCtx → Sub → Name → Maybe Tm
termFor ∅           _        n = nothing
termFor (M ▹ x ∶ _) ⟨⟩       n = nothing
termFor (M ▹ x ∶ _) (θ ,ₛ t) n = if n ==ℕ x then just t else termFor M θ n
