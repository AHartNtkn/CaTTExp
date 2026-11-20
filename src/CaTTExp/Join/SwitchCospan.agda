------------------------------------------------------------------------
-- The cospan completion is parametric in the law switches
-- (notes/design-decisions.md §1.7, ledger E12). The side condition
-- computes in V + S, where S ranges over the laws visible on pasting
-- diagrams (the inner composite-crossing law and R); the default is
-- V, no switch on. The settings offered, vS and allS, are in
-- CaTTExp.Join.SwitchLaws.
--
-- A law setting S presents its comparison graph by step lists, as in
-- CaTTExp.Join.BoundedReach: cells A_S, inner steps nextE_S and seed
-- steps nextP_S. The cospan completion (CaTTExp.Join.Cospan) of that
-- quiver is defined for every setting; nothing in it refers to T₁₂.
--
-- Switching laws on is a quotient map of free objects that is the
-- identity on letters (BoundedReach.Transport). So it sends each inner
-- step to an inner step and each seed step to a seed step. Here:
--
--   ext        the extension of a switch map to the completions
--              (j α I R ↦ j (f α) (f I) (f R));
--   ext-~      it respects the completion equations;
--   ext-++     it respects composition;
--   ext-ι      it agrees with the switch map on original paths
--              (these three are CospanNatural.Map's map-~, map-++ and
--              map-ι, re-exported for letter maps);
--   ext-seeds  it maps seed lists letterwise, so seed-list invariance
--              (Cospan.seeds-~) is carried along;
--   ext-∘      switching on in two stages is switching on at once;
--   ext-id     the identity switch extends to the identity.
--
-- Where the law equations enter depends on the level. When the
-- vertices are 3-cells, the laws (which relate 4-cells) are equations
-- between inner words and the switch map is idS. CaTTExp.Join.SwitchLaws
-- machine-checks that the switched laws keep seed lists in
-- raw T-syntax (Part A) and that inner-word equations keep seed lists
-- in the completion (Part B); the link between the two, and that the
-- 3-cell setting is switch-independent (Part C, a definition), are on
-- paper. When the vertices are 4-cells, the
-- laws enter through the quotient on cells; that the switch map is
-- then a Switch (5-letters keep their kind) is not mechanized, since
-- there is no raw 5-dimensional syntax yet (joining-completion.md §8).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver
open import CaTTExp.Join.BoundedReach using (_∈_)
import CaTTExp.Join.Cospan as Cospan
import CaTTExp.Join.CospanNatural as CospanNatural

module CaTTExp.Join.SwitchCospan where

-- A law setting's comparison graph, as step lists.
record Setting : Set₁ where
  field
    Cell  : Set
    nextE : Cell → List Cell
    nextP : Cell → List Cell

  Inner : Cell → Cell → Set
  Inner x y = y ∈ nextE x

  Seed : Cell → Cell → Set
  Seed x y = y ∈ nextP x

  module Completion = Cospan Inner Seed

open Setting

-- A switch map: identity on letters, so steps go to steps.
record Switch (S S′ : Setting) : Set where
  field
    cell  : Cell S → Cell S′
    stepE : ∀ {x y} → Inner S x y → Inner S′ (cell x) (cell y)
    stepP : ∀ {x y} → Seed S x y → Seed S′ (cell x) (cell y)
open Switch

module Ext {S S′ : Setting} (σ : Switch S S′) where

  private
    module C  = Cospan (Inner S) (Seed S)
    module C′ = Cospan (Inner S′) (Seed S′)
    module N  = CospanNatural (Inner S) (Seed S) (Inner S′) (Seed S′)
    letter : ∀ {x y} → Seed S x y → N.SeedWord (cell σ x) (cell σ y)
    letter α = N.sw [] (stepP σ α) []
    module M = N.Map (cell σ) (λ e → stepE σ e ∷ []) letter

  ext : ∀ {a b} → C.Word a b → C′.Word (cell σ a) (cell σ b)
  ext = M.mapW

  extI : ∀ {a b} → C.IPath a b → C′.IPath (cell σ a) (cell σ b)
  extI []      = []
  extI (e ∷ R) = stepE σ e ∷ extI R

  extI-mapI : ∀ {a b} (R : C.IPath a b) → M.mapI R ≡ extI R
  extI-mapI []      = refl
  extI-mapI (e ∷ R) = cong (stepE σ e ∷_) (extI-mapI R)

  -- On generators the extension is letterwise.
  ext-inn : ∀ {a b c} (e : Inner S a b) (w : C.Word b c) →
            ext (C.inn e ∷ w) ≡ C′.inn (stepE σ e) ∷ ext w
  ext-inn e w = refl

  ext-jn : ∀ {s t m u c} (α : Seed S s t) (I : C.IPath t m) (R : C.IPath u m)
           (w : C.Word u c) →
           ext (C.jn α I R ∷ w) ≡ C′.jn (stepP σ α) (extI I) (extI R) ∷ ext w
  ext-jn α I R w = cong₂ (λ I′ R′ → C′.jn (stepP σ α) I′ R′ ∷ ext w)
                         (extI-mapI I) (extI-mapI R)

  ext-~ : ∀ {a b} {w w′ : C.Word a b} → w C.~ w′ → ext w C′.~ ext w′
  ext-~ = M.map-~

  ext-++ : ∀ {a b c} (p : C.Word a b) (q : C.Word b c) →
           ext (p ++ᵖ q) ≡ ext p ++ᵖ ext q
  ext-++ = M.map-++

  ext-ι : ∀ {a b} (p : Path C.Orig a b) → ext (C.ι p) C′.~ C′.ι (M.mapO p)
  ext-ι = M.map-ι

  -- Seed lists are mapped letterwise.
  seedsMap : ∀ {a b} → C.Word a b → List C′.Seed
  seedsMap []               = []
  seedsMap (C.inn e ∷ w)    = seedsMap w
  seedsMap (C.jn α I R ∷ w) = C′.seed (stepP σ α) ∷ seedsMap w

  ext-seeds : ∀ {a b} (w : C.Word a b) → C′.seeds (ext w) ≡ seedsMap w
  ext-seeds []               = refl
  ext-seeds (C.inn e ∷ w)    = ext-seeds w
  ext-seeds (C.jn α I R ∷ w) = cong (_ ∷_) (ext-seeds w)

  seedsMap-~ : ∀ {a b} {w w′ : C.Word a b} → w C.~ w′ → seedsMap w ≡ seedsMap w′
  seedsMap-~ {w = w} {w′} p =
    trans (sym (ext-seeds w)) (trans (C′.seeds-~ (ext-~ p)) (ext-seeds w′))

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x′ y y′ z z′} →
        x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

-- Switching on in two stages is switching on at once.
_∘S_ : ∀ {S S′ S″} → Switch S′ S″ → Switch S S′ → Switch S S″
cell  (τ ∘S σ) x = cell τ (cell σ x)
stepE (τ ∘S σ) e = stepE τ (stepE σ e)
stepP (τ ∘S σ) α = stepP τ (stepP σ α)

idS : ∀ {S} → Switch S S
cell  idS x = x
stepE idS e = e
stepP idS α = α

module _ {S S′ S″ : Setting} (σ : Switch S S′) (τ : Switch S′ S″) where
  private
    module C = Cospan (Inner S) (Seed S)
    module C″ = Cospan (Inner S″) (Seed S″)
    module Eσ = Ext σ
    module Eτ = Ext τ
    module Eτσ = Ext (τ ∘S σ)

  extI-∘ : ∀ {a b} (R : C.IPath a b) → Eτσ.extI R ≡ Eτ.extI (Eσ.extI R)
  extI-∘ []      = refl
  extI-∘ (e ∷ R) = cong (stepE τ (stepE σ e) ∷_) (extI-∘ R)

  ext-∘ : ∀ {a b} (w : C.Word a b) → Eτσ.ext w ≡ Eτ.ext (Eσ.ext w)
  ext-∘ []               = refl
  ext-∘ (C.inn e ∷ w)    = cong (_ ∷_) (ext-∘ w)
  ext-∘ (C.jn α I R ∷ w) =
    trans (Eτσ.ext-jn α I R w)
      (trans (cong₃ (λ I′ R′ w′ → C″.jn (stepP τ (stepP σ α)) I′ R′ ∷ w′)
                    (extI-∘ I) (extI-∘ R) (ext-∘ w))
        (trans (sym (Eτ.ext-jn (stepP σ α) (Eσ.extI I) (Eσ.extI R) (Eσ.ext w)))
               (cong Eτ.ext (sym (Eσ.ext-jn α I R w)))))

module _ {S : Setting} where
  private
    module C = Cospan (Inner S) (Seed S)
    module E = Ext (idS {S})

  extI-id : ∀ {a b} (R : C.IPath a b) → E.extI R ≡ R
  extI-id []      = refl
  extI-id (e ∷ R) = cong (e ∷_) (extI-id R)

  ext-id : ∀ {a b} (w : C.Word a b) → E.ext w ≡ w
  ext-id []               = refl
  ext-id (C.inn e ∷ w)    = cong (_ ∷_) (ext-id w)
  ext-id (C.jn α I R ∷ w) =
    trans (E.ext-jn α I R w)
          (cong₃ (λ I′ R′ w′ → C.jn α I′ R′ ∷ w′) (extI-id I) (extI-id R) (ext-id w))
