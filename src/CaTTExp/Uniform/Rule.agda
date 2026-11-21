------------------------------------------------------------------------
-- The kernel's side condition SC, decided over a free-object layer
-- (spec/02-lax-core.md §2.2–2.3; ledger S3).
--
-- The spec states the side condition of (coh_S) as
--
--   SC(Γ, t →_A u)  :⟺  F_{V+S}(Γ) has a cell c : ⟦t⟧ → ⟦u⟧
--                        with supp(c) = all generators.
--
-- A cell one dimension up is a chronological path of contextual
-- generating letters (spec §2.3 step 3; r10 Response 3, "Reachability
-- and comparisons": "any witness expands into chronological generating
-- steps"). Existence of a cell is therefore existence of a path, and
-- the support of the cell is the union of the supports of its letters
-- and of its two faces. This module works over any `Layer`, which
-- packages exactly the data the decision procedure reads:
--
--   Cell, _≟_     cells of the layer in normal form, with decidable
--                 equality (r10 Response 3 "Building the normal forms");
--   out, tgt      the finite contextual alphabet out of a cell (K50),
--                 each letter with its target;
--   Supp, supp,   supports, their union, and the test "is the
--   suppL, _∪_,   support everything". The fullness test is a
--   full          parameter, so the module is independent of how the
--                 support of V + S is read (ledger S1).
--
-- and, separately (`Graded`), a bound on the length of every path
-- between two given cells (the positive gradings (K45)/(K50)).
--
-- Proved here, for every layer:
--   sc?          SC is decidable, given a grading bound;
--   coherence    an identity on a cell of full support is a witness
--                (the coherence case of spec §2.2);
--   Transport    a setting map that sends letters to letters and full
--                supports to full supports sends SC to SC (spec §2.3,
--                "Imports run upwards").
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; _≤_; z≤n; s≤s)
open import CaTTExp.Uniform.ListKit

module CaTTExp.Uniform.Rule where

record Layer : Set₁ where
  field
    Cell   : Set
    _≟_    : (x y : Cell) → Dec (x ≡ y)
    Letter : Set
    out    : Cell → List Letter
    tgt    : Letter → Cell
    Supp   : Set
    supp   : Cell → Supp
    suppL  : Letter → Supp
    _∪_    : Supp → Supp → Supp
    full   : Supp → Bool

module _ (L : Layer) where
  open Layer L

  -- A cell one dimension up, as a chronological path of letters.
  infixr 5 _◅[_]_
  data Path : Cell → Cell → Set where
    ε      : ∀ {x} → Path x x
    _◅[_]_ : ∀ {x z} (ℓ : Letter) → ℓ ∈L out x → Path (tgt ℓ) z → Path x z

  lenP : ∀ {x z} → Path x z → Nat
  lenP ε            = zero
  lenP (_ ◅[ _ ] p) = suc (lenP p)

  -- Support of a path: its faces and every letter.
  suppP : ∀ {x z} → Path x z → Supp
  suppP {x} ε            = supp x
  suppP {x} (ℓ ◅[ _ ] p) = supp x ∪ (suppL ℓ ∪ suppP p)

  -- The side condition.
  SC : Cell → Cell → Set
  SC x z = Σ (Path x z) λ p → T (full (suppP p))

  -- The coherence case: the identity on a cell of full support.
  coherence : ∀ {x} → T (full (supp x)) → SC x x
  coherence f = ε , f

  -- All paths of length at most k out of a cell.
  paths : Nat → (x : Cell) → List (Σ Cell (Path x))
  paths zero    x = (x , ε) ∷ []
  paths (suc k) x =
    (x , ε) ∷ concatK (mapK (λ lm → mapK (λ zp → fst zp , (fst lm ◅[ snd lm ] snd zp))
                                         (paths k (tgt (fst lm))))
                            (withMem (out x)))

  paths-complete : ∀ k {x z} (p : Path x z) → lenP p ≤ k → (z , p) ∈L paths k x
  paths-complete zero    ε _ = here
  paths-complete (suc k) ε _ = here
  paths-complete (suc k) {x} (ℓ ◅[ m ] p) (s≤s le) =
    there (∈-concat⁺ _ (∈-map⁺ (λ zp → fst zp , (ℓ ◅[ m ] snd zp)) (paths-complete k p le))
                       (∈-map⁺ (λ lm → mapK (λ zp → fst zp , (fst lm ◅[ snd lm ] snd zp))
                                              (paths k (tgt (fst lm))))
                               (withMem-has (out x) m)))

  -- Search a list of paths for one ending at z with full support.
  private
    hit? : ∀ {x} z (zp : Σ Cell (Path x)) →
           Dec (Σ (Path x z) λ p → (zp ≡ (z , p)) × T (full (suppP p)))
    hit? z (z′ , p) with z′ ≟ z
    ... | no ne = no λ { (_ , refl , _) → ne refl }
    ... | yes refl with T? (full (suppP p))
    ...   | yes f = yes (p , refl , f)
    ...   | no ¬f = no λ { (_ , refl , f) → ¬f f }

  record Graded : Set where
    field
      bound  : Cell → Cell → Nat
      graded : ∀ {x z} (p : Path x z) → lenP p ≤ bound x z

  module Decide (G : Graded) where
    open Graded G

    -- SC is decidable.
    sc? : ∀ x z → Dec (SC x z)
    sc? x z with first? (hit? z) (paths (bound x z) x)
    ... | yes (_ , _ , p , _ , f) = yes (p , f)
    ... | no ¬h = no λ { (p , f) →
          ¬h ((z , p) , paths-complete (bound x z) p (graded p) , p , refl , f) }

    ⌊sc⌋ : Cell → Cell → Bool
    ⌊sc⌋ x z with sc? x z
    ... | yes _ = true
    ... | no  _ = false

    ⌊sc⌋-sound : ∀ x z → T (⌊sc⌋ x z) → SC x z
    ⌊sc⌋-sound x z t with sc? x z
    ... | yes s = s

    ⌊sc⌋-complete : ∀ x z → SC x z → T (⌊sc⌋ x z)
    ⌊sc⌋-complete x z s with sc? x z
    ... | yes _ = tt
    ... | no ¬s = ¬s s

------------------------------------------------------------------------
-- Imports run upwards (spec §2.3): a map of layers that sends letters
-- out of x to letters out of f x, commutes with supports through a
-- union-preserving map g, and sends full supports to full supports,
-- sends every witness of SC to a witness of SC.

module Transport (L L′ : Layer) where
  private
    module L  = Layer L
    module L′ = Layer L′

  record Map : Set where
    field
      cell     : L.Cell → L′.Cell
      letter   : L.Letter → L′.Letter
      out-map  : ∀ {x ℓ} → ℓ ∈L L.out x → letter ℓ ∈L L′.out (cell x)
      tgt-map  : ∀ ℓ → L′.tgt (letter ℓ) ≡ cell (L.tgt ℓ)
      supp-map : L.Supp → L′.Supp
      supp-c   : ∀ x → supp-map (L.supp x) ≡ L′.supp (cell x)
      supp-l   : ∀ ℓ → supp-map (L.suppL ℓ) ≡ L′.suppL (letter ℓ)
      supp-∪   : ∀ s t → supp-map (s L.∪ t) ≡ (supp-map s L′.∪ supp-map t)
      full-map : ∀ s → T (L.full s) → T (L′.full (supp-map s))

  module _ (M : Map) where
    open Map M

    mapP : ∀ {x z} → Path L x z → Path L′ (cell x) (cell z)
    mapP ε            = ε
    mapP (ℓ ◅[ m ] p) = letter ℓ ◅[ out-map m ] subst (λ y → Path L′ y _) (sym (tgt-map ℓ)) (mapP p)

    private
      supp-subst : ∀ {y y′ z} (e : y ≡ y′) (p : Path L′ y z) →
                   suppP L′ (subst (λ w → Path L′ w z) e p) ≡ suppP L′ p
      supp-subst refl p = refl

    mapP-supp : ∀ {x z} (p : Path L x z) → supp-map (suppP L p) ≡ suppP L′ (mapP p)
    mapP-supp ε = supp-c _
    mapP-supp {x} (ℓ ◅[ m ] p) =
      trans (supp-∪ _ _)
        (cong₂ L′._∪_ (supp-c x)
          (trans (supp-∪ _ _)
            (cong₂ L′._∪_ (supp-l ℓ)
              (trans (mapP-supp p) (sym (supp-subst (sym (tgt-map ℓ)) (mapP p)))))))

    sc-map : ∀ {x z} → SC L x z → SC L′ (cell x) (cell z)
    sc-map (p , f) = mapP p , subst (λ s → T (L′.full s)) (mapP-supp p) (full-map _ f)
