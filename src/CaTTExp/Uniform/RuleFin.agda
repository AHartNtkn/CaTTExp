------------------------------------------------------------------------
-- The side condition SC decided without a length bound
-- (spec/02-lax-core.md §2.3 step 3; r10 Response 3, "Reachability and
--  comparisons"; ledger S3a, S3b).
--
-- CaTTExp.Uniform.Rule decides SC from a bound on the length of every
-- path between two cells (`Graded`). Free objects of V + S can contain
-- loops, and then no such bound exists:
--   * in V at degree four on Σ[2] ∨ Σ[2], the loop H of (K34) has
--     pairwise distinct powers H^k : w → w ((K45));
--   * at degree five on the suspended 2 × 2 grid in setting
--     {inner law, R}, the positional square between the two expansions
--     of the full crossing is a loop (CaTTExp.Uniform.GridFive).
-- r10 Response 3 decides reachability by breadth-first search over the
-- finite list of vertices at fixed faces and weight, with no bound on
-- the witness. This module does the same for SC, which also asks the
-- support of the witness to be full: it searches the finite graph of
-- states (cell, support accumulated so far).
--
-- Hypotheses (module DecideFin):
--   ∪-assoc   the union of supports is associative (so the support of
--             a path can be accumulated from left to right);
--   _≟S_      supports have decidable equality;
--   UC, US    finite lists of cells and of supports, with x ∈ UC and
--             supp x ∈ US, closed under the steps: if y ∈ UC, a ∈ US
--             and ℓ ∈ out y, then tgt ℓ ∈ UC and
--             a ∪ (suppL ℓ ∪ supp (tgt ℓ)) ∈ US.
-- Proved: sc? : Dec (SC x z) for every z, with no length bound.
--
-- KernelDec (CaTTExp.Uniform.KernelDec) takes any decision of SC, so
-- either this module or Rule.Decide can feed the kernel.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; lengthL)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Rule
import CaTTExp.Uniform.FiniteGraph as FG

module CaTTExp.Uniform.RuleFin where

module DecideFin
  (L : Layer)
  (let open Layer L)
  (∪-assoc : ∀ a b c → (a ∪ b) ∪ c ≡ a ∪ (b ∪ c))
  (_≟S_ : (a b : Supp) → Dec (a ≡ b))
  where

  -- States: a cell and the support accumulated so far.
  State : Set
  State = Σ Cell λ _ → Supp

  _≟St_ : (s t : State) → Dec (s ≡ t)
  (x , a) ≟St (y , b) with x ≟ y | a ≟S b
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }

  upd : Supp → Letter → Supp
  upd a ℓ = a ∪ (suppL ℓ ∪ supp (tgt ℓ))

  next : State → List State
  next (y , a) = mapK (λ ℓ → tgt ℓ , upd a ℓ) (out y)

  open FG _≟St_ next

  -- The support accumulated along a path, from a starting value.
  glue : ∀ {y z} → Supp → Path L y z → Supp
  glue a ε            = a
  glue a (ℓ ◅[ _ ] p) = glue (upd a ℓ) p

  private
    glue-∪ : ∀ {y z} b (p : Path L y z) → glue (b ∪ supp y) p ≡ b ∪ suppP L p
    glue-∪ b ε = refl
    glue-∪ {y} b (ℓ ◅[ m ] p) =
      trans (cong (λ s → glue s p) (sym (∪-assoc (b ∪ supp y) (suppL ℓ) (supp (tgt ℓ)))))
        (trans (glue-∪ ((b ∪ supp y) ∪ suppL ℓ) p)
          (trans (∪-assoc (b ∪ supp y) (suppL ℓ) (suppP L p))
                 (∪-assoc b (supp y) (suppL ℓ ∪ suppP L p))))

  glue-supp : ∀ {x z} (p : Path L x z) → glue (supp x) p ≡ suppP L p
  glue-supp ε = refl
  glue-supp {x} (ℓ ◅[ m ] p) =
    trans (cong (λ s → glue s p) (sym (∪-assoc (supp x) (suppL ℓ) (supp (tgt ℓ)))))
      (trans (glue-∪ (supp x ∪ suppL ℓ) p) (∪-assoc (supp x) (suppL ℓ) (suppP L p)))

  -- Paths of letters are paths of states, and conversely.
  path→star : ∀ {y z} a (p : Path L y z) → Star (y , a) (z , glue a p)
  path→star a ε            = ε
  path→star a (ℓ ◅[ m ] p) = ∈-map⁺ (λ ℓ → tgt ℓ , upd a ℓ) m ◅ path→star (upd a ℓ) p

  star→path : ∀ {y z a b} → Star (y , a) (z , b) → Σ (Path L y z) λ p → glue a p ≡ b
  star→path ε = ε , refl
  star→path {y} {a = a} (m ◅ s) with ∈-map⁻ (λ ℓ → tgt ℓ , upd a ℓ) (out y) m
  ... | ℓ , mℓ , refl with star→path s
  ...   | p , e = (ℓ ◅[ mℓ ] p) , e

  module _ (UC : List Cell) (US : List Supp)
           (closedC : ∀ {y ℓ} → y ∈L UC → ℓ ∈L out y → tgt ℓ ∈L UC)
           (closedS : ∀ {y a ℓ} → y ∈L UC → a ∈L US → ℓ ∈L out y → upd a ℓ ∈L US)
           where

    U : List State
    U = concatK (mapK (λ y → mapK (λ a → y , a) US) UC)

    U-has : ∀ {y a} → y ∈L UC → a ∈L US → (y , a) ∈L U
    U-has {y} {a} my ma =
      ∈-concat⁺ _ (∈-map⁺ (λ a → y , a) ma) (∈-map⁺ (λ y → mapK (λ a → y , a) US) my)

    U-split : ∀ {y a} → (y , a) ∈L U → (y ∈L UC) × (a ∈L US)
    U-split {y} {a} m with ∈-concat⁻ (mapK (λ y → mapK (λ a → y , a) US) UC) m
    ... | ys , m₁ , m₂ with ∈-map⁻ (λ y → mapK (λ a → y , a) US) UC m₂
    ...   | y′ , my′ , refl with ∈-map⁻ (λ a → y′ , a) US m₁
    ...     | a′ , ma′ , refl = my′ , ma′

    closed : ∀ {s t} → s ∈L U → t ∈L next s → t ∈L U
    closed {y , a} ms mt with U-split ms | ∈-map⁻ (λ ℓ → tgt ℓ , upd a ℓ) (out y) mt
    ... | my , ma | ℓ , mℓ , refl = U-has (closedC my mℓ) (closedS my ma mℓ)

    module _ {x} (xC : x ∈L UC) (xS : supp x ∈L US) where

      reached : List State
      reached = reachSet (lengthL U) (x , supp x)

      private
        hit? : ∀ z (s : State) →
               Dec (Σ Supp λ a → (s ≡ (z , a)) × T (full a))
        hit? z (z′ , a) with z′ ≟ z
        ... | no ne = no λ { (_ , refl , _) → ne refl }
        ... | yes refl with T? (full a)
        ...   | yes f = yes (a , refl , f)
        ...   | no ¬f = no λ { (_ , refl , f) → ¬f f }

      -- SC is decidable, with no bound on the length of the witness.
      sc? : ∀ z → Dec (SC L x z)
      sc? z with first? (hit? z) reached
      ... | yes ((s , a) , ms , a′ , refl , f)
            with star→path (reachSet-sound (lengthL U) (x , supp x) ms)
      ...   | p , e = yes (p , subst (λ s → T (full s))
                                       (trans (sym e) (glue-supp p)) f)
      sc? z | no ¬h = no λ { (p , f) →
          ¬h ((z , suppP L p) ,
              subst (λ b → (z , b) ∈L reached) (glue-supp p)
                (Saturate.reachSet-complete U closed (U-has xC xS)
                  (path→star (supp x) p)) ,
              suppP L p , refl , f) }
