------------------------------------------------------------------------
-- A deterministic decision procedure for Finster–Mimram's pasting
-- judgments, proved sound *and complete*.
--
-- The rules pss/pse/psd are not syntax directed (psd can be applied
-- anywhere), but the only freedom is how far to "descend" with psd
-- before the next pse. Since each psd lowers the dimension of the
-- dangling cell by one, the descent is forced by the dimension of the
-- next object being attached. So reading Γ left to right while keeping
-- one dangling cell decides Γ ⊢ps.
--
--   run Γ          : the dangling cell after reading all of Γ, with its
--                    derivation (the one that never descends past what
--                    the next pse needs);
--   run-complete   : every derivation Γ ⊢ps x ∶ A is reached from
--                    `run Γ` by psd steps;
--   checkPs        : decides Γ ⊢ps, with checkPs-complete.
--
-- No hypothesis on the signature is needed: types in a pasting
-- derivation are built from ⋆, arr and variables only.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.PastingCheck (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊

PsState : Ctx → Set
PsState Γ = Σ Nat λ x → Σ Ty λ A → Γ ⊢ps x ∶ A

------------------------------------------------------------------------
-- Descent: apply psd until the dangling cell has dimension n.

mutual
  descend : Nat → ∀ {Γ} x A → Γ ⊢ps x ∶ A → Maybe (PsState Γ)
  descend n x A d = descend′ n x A d (dim A ==ℕ n)

  descend′ : Nat → ∀ {Γ} x A → Γ ⊢ps x ∶ A → Bool → Maybe (PsState Γ)
  descend′ n x A                       d true  = just (x , A , d)
  descend′ n f (arr A (var x) (var y)) d false = descend n y A (psd d)
  descend′ n f ⋆                       d false = nothing
  descend′ n f (arr A (var x) (coh _ _ _)) d false = nothing
  descend′ n f (arr A (var x) (cst _))     d false = nothing
  descend′ n f (arr A (coh _ _ _) _)       d false = nothing
  descend′ n f (arr A (cst _) _)           d false = nothing

------------------------------------------------------------------------
-- Attaching one more (object, arrow) pair.

private
  whenEq : ∀ {Z : Set} (X Y : Ty) → (X ≡ Y → Maybe Z) → Maybe Z
  whenEq X Y k = guard (X ==Ty Y) (λ p → k (==Ty-sound X Y p))

  pse′ : ∀ {Γ x A′ A B} → A′ ≡ A → arr A′ (var x) (var (len Γ)) ≡ B →
         Γ ⊢ps x ∶ A′ → (Γ ▸ A ▸ B) ⊢ps suc (len Γ) ∶ B
  pse′ refl refl d = pse d

attach : ∀ {Γ} x A′ → Γ ⊢ps x ∶ A′ → (A B : Ty) → Maybe (PsState (Γ ▸ A ▸ B))
attach {Γ} x A′ d A B =
  whenEq A′ A λ e →
  whenEq (arr A′ (var x) (var (len Γ))) B λ e′ →
  just (suc (len Γ) , B , pse′ e e′ d)

extend : ∀ {Γ} → PsState Γ → (A B : Ty) → Maybe (PsState (Γ ▸ A ▸ B))
extend (x₀ , A₀ , d₀) A B =
  descend (dim A) x₀ A₀ d₀ >>= λ s → attach (fst s) (fst (snd s)) (snd (snd s)) A B

run : (Γ : Ctx) → Maybe (PsState Γ)
run ε               = nothing
run (ε ▸ ⋆)         = just (0 , ⋆ , pss)
run (ε ▸ arr _ _ _) = nothing
run (Γ ▸ A ▸ B)     = run Γ >>= λ s → extend s A B

private
  toPs : ∀ {Γ} → PsState Γ → Maybe (Γ ⊢ps)
  toPs (x , ⋆ , d)         = just (ps d)
  toPs (x , arr _ _ _ , d) = nothing

checkPs : (Γ : Ctx) → Maybe (Γ ⊢ps)
checkPs Γ = run Γ >>= λ s → descend 0 (fst s) (fst (snd s)) (snd (snd s)) >>= toPs

------------------------------------------------------------------------
-- Completeness.

private
  data _≤_ : Nat → Nat → Set where
    z≤n : ∀ {n} → zero ≤ n
    s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

  ≤-refl : ∀ n → n ≤ n
  ≤-refl zero    = z≤n
  ≤-refl (suc n) = s≤s (≤-refl n)

  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step z≤n     = z≤n
  ≤-step (s≤s p) = s≤s (≤-step p)

  suc-≢ : ∀ {m n} → m ≤ n → (suc n ==ℕ m) ≡ false
  suc-≢ z≤n     = refl
  suc-≢ (s≤s p) = suc-≢ p

  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

  ==ℕ-refl′ : ∀ n → (n ==ℕ n) ≡ true
  ==ℕ-refl′ n = T→≡ (==ℕ-refl n)

-- Types that occur in pasting derivations.
data PsTy : Ty → Set where
  ⋆ₚ   : PsTy ⋆
  arrₚ : ∀ {A x y} → PsTy A → PsTy (arr A (var x) (var y))

ps-ty : ∀ {Γ x A} → Γ ⊢ps x ∶ A → PsTy A
ps-ty pss     = ⋆ₚ
ps-ty (pse d) = arrₚ (ps-ty d)
ps-ty (psd d) with ps-ty d
... | arrₚ p = p

==Ty-refl-ps : ∀ {A} → PsTy A → T (A ==Ty A)
==Ty-refl-ps ⋆ₚ                     = tt
==Ty-refl-ps (arrₚ {A} {x} {y} p) = and3 (==Ty-refl-ps p) (==ℕ-refl x) (==ℕ-refl y)
  where
  and3 : ∀ {a b c} → T a → T b → T c → T (a ∧ b ∧ c)
  and3 {true} {true} _ _ c = c

-- Reach x A z C: the dangling cell (z, C) is obtained from (x, A) by
-- zero or more psd steps.
data Reach : Nat → Ty → Nat → Ty → Set where
  here : ∀ {x A} → Reach x A x A
  down : ∀ {f A x y z C} → Reach y A z C → Reach f (arr A (var x) (var y)) z C

reach-snoc : ∀ {x₀ A₀ f A x y} → Reach x₀ A₀ f (arr A (var x) (var y)) → Reach x₀ A₀ y A
reach-snoc here     = down here
reach-snoc (down r) = down (reach-snoc r)

private
  reach-dim : ∀ {x A z C} → Reach x A z C → dim C ≤ dim A
  reach-dim {A = A} here = ≤-refl (dim A)
  reach-dim (down r)     = ≤-step (reach-dim r)

descend-reach : ∀ {Γ x A z C} (d : Γ ⊢ps x ∶ A) → Reach x A z C →
                Σ (Γ ⊢ps z ∶ C) λ d′ → descend (dim C) x A d ≡ just (z , C , d′)
descend-reach {x = x} {A} d here =
  d , cong (descend′ (dim A) x A d) (==ℕ-refl′ (dim A))
descend-reach {x = f} {arr A (var x) (var y)} {C = C} d (down r) =
  let (d′ , eq) = descend-reach (psd d) r in
  d′ , trans (cong (descend′ (dim C) f (arr A (var x) (var y)) d) (suc-≢ (reach-dim r))) eq

private
  bind-≡ : ∀ {a b} {A : Set a} {B : Set b} {m : Maybe A} {x : A} (f : A → Maybe B) →
           m ≡ just x → (m >>= f) ≡ f x
  bind-≡ f refl = refl

  guard-≡ : ∀ {a} {Z : Set a} b (k : T b → Maybe Z) (p : T b) → guard b k ≡ k p
  guard-≡ true k tt = refl

attach-complete : ∀ {Γ x A} (d : Γ ⊢ps x ∶ A) →
                  Σ ((Γ ▸ A ▸ arr A (var x) (var (len Γ))) ⊢ps suc (len Γ) ∶ arr A (var x) (var (len Γ)))
                    λ d′ → attach x A d A (arr A (var x) (var (len Γ)))
                           ≡ just (suc (len Γ) , arr A (var x) (var (len Γ)) , d′)
attach-complete {Γ} {x} {A} d =
  _ , trans (guard-≡ (A ==Ty A) _ p₁) (guard-≡ (B ==Ty B) _ p₂)
  where
  B = arr A (var x) (var (len Γ))
  p₁ = ==Ty-refl-ps (ps-ty d)
  p₂ = ==Ty-refl-ps (ps-ty (pse d))

run-complete : ∀ {Γ x A} → Γ ⊢ps x ∶ A →
               Σ (PsState Γ) λ s → (run Γ ≡ just s) × Reach (fst s) (fst (snd s)) x A
run-complete pss = (0 , ⋆ , pss) , refl , here
run-complete (psd d) =
  let (s , eq , r) = run-complete d in s , eq , reach-snoc r
run-complete (pse {Γ} {x} {A} d) =
  let ((x₀ , A₀ , d₀) , eq , r) = run-complete d
      (d′ , eq′) = descend-reach d₀ r
      (d″ , eq″) = attach-complete d′
  in (suc (len Γ) , arr A (var x) (var (len Γ)) , d″)
     , trans (bind-≡ (λ s → extend s A (arr A (var x) (var (len Γ)))) eq)
             (trans (bind-≡ (λ s → attach (fst s) (fst (snd s)) (snd (snd s)) A _) eq′) eq″)
     , here

checkPs-complete : ∀ {Γ} → Γ ⊢ps → T (is-just (checkPs Γ))
checkPs-complete {Γ} (ps d) =
  let (s , eq , r) = run-complete d
      (d′ , eq′) = descend-reach (snd (snd s)) r
  in subst (λ m → T (is-just m))
       (sym (trans (bind-≡ (λ s → descend 0 (fst s) (fst (snd s)) (snd (snd s)) >>= toPs) eq)
                   (bind-≡ toPs eq′)))
       tt
