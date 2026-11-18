------------------------------------------------------------------------
-- The orientation family L_ε (notes/closed-structure.md, D.3).
--
-- ε : hom-dimension → Bool says which hom-dimensions are reversed
-- (true = reversed). L_ε computes supports in
--     ν(Θ₁ ⊗_ε … ⊗_ε Θₙ),   X ⊗_ε Y := D_ε (D_ε X ⊗ D_ε Y),
-- where D_ε reverses the cells of the dimensions in ε. On the tables
-- of a pasting diagram, D_ε swaps the i-dimensional source and target
-- pieces exactly when (i+1)-cells are reversed:
--     (D_ε Θ)^sg_i = Θ^{ε(i+1)·sg}_i.
-- So T_ε's table is the AM tensor of the twisted pieces, twisted once
-- more at the end:
--     (T_ε)^sg_k = (⊗ of the D_ε Θⱼ)^{ε(k+1)·sg}_k.
-- The cells and the face order are unchanged by D_ε, so only the
-- sides of the tables change; the top chain does not depend on signs.
--
-- Results:
--   graySideε (λ _ → false) ≡ graySide       (no reversal: L)
--   graySideε (λ _ → true)  ≡ graySide       (total reversal: L again)
-- by `chainTε-const`. Alternating ε gives the factor-reversed tables
-- (Gray.OrientRev). Examples (the interchanger; the twisted
-- tensor of the note's D.1 example) are in Gray.OrientExamples.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Orient (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊

Orient : Set
Orient = Nat → Bool

flipIf : Bool → Bool → Bool
flipIf e sg = if e then not sg else sg

pieceε : Orient → Hom → Nat → Bool → List Nat
pieceε o h i sg = piece h i (flipIf (o (suc i)) sg)

-- The AM tensor of the D_ε Θⱼ.
chainε : Orient → Bool → Nat → List Hom → TSet
chainε o sg k []       = if k ==ℕ 0 then [] ∷ [] else []
chainε o sg k (h ∷ hs) =
  concatMap (λ i → prod1 (pieceε o h i sg) (chainε o (if odd i then not sg else sg) (k ∸ i) hs))
            (filter (λ i → i <ℕ suc k) (upto k))

-- (T_ε)^sg_k.
chainTε : Orient → Bool → Nat → List Hom → TSet
chainTε o sg k hs = chainε o (flipIf (o (suc k)) sg) k hs

lowerTε : Orient → Nat → List Hom → TSet
lowerTε o zero    hs = []
lowerTε o (suc m) hs = lowerTε o m hs ++ chainTε o false m hs ++ chainTε o true m hs

topTε : Orient → List Hom → TSet
topTε o hs = chainTε o true (dimK hs) hs

fullTε : Orient → List Hom → TSet
fullTε o hs = lowerTε o (dimK hs) hs ++ topTε o hs

bdryTε : Orient → Bool → List Hom → TSet
bdryTε o sg hs = lowerTε o (dimK hs ∸ 1) hs ++ chainTε o sg (dimK hs ∸ 1) hs

module _ (o : Orient) where
  mutual
    topSε : Tm → TSet
    topSε (var v)              = (v ∷ []) ∷ []
    topSε (cst _)              = []
    topSε (coh Θ ⋆ ρ)          = []
    topSε (coh Θ (arr A t u) ρ) =
      applyF (topsSubε ρ) (if cohCaseε Θ A t u then [] else topTε o (homs Θ))

    topsSubε : Sub → List TSet
    topsSubε ⟨⟩       = []
    topsSubε (ρ ,ₛ t) = topsSubε ρ ++ (topSε t ∷ [])

    suppTyε : Ty → TSet
    suppTyε ⋆                      = []
    suppTyε (arr ⋆ _ _)            = []
    suppTyε (arr (arr B s s') t u) = suppTyε (arr B s s') ++ topSε t ++ topSε u

    suppε : Tm → Ty → TSet
    suppε t A = topSε t ++ suppTyε A

    cohCaseε : Ctx → Ty → Tm → Tm → Bool
    cohCaseε Θ ⋆ t u = false
    cohCaseε Θ A@(arr _ _ _) t u =
      endsOK Θ A ∧ sameDown Θ (suppε t A) (fullTε o (homs Θ))
                 ∧ sameDown Θ (suppε u A) (fullTε o (homs Θ))

  opCaseε : Ctx → Ty → Tm → Tm → Bool
  opCaseε Θ ⋆ t u = opCase Θ ⋆ t u
  opCaseε Θ A@(arr _ _ _) t u =
    endsOK Θ A ∧ (dim A ==ℕ dimK (homs Θ))
    ∧ sameDown Θ (suppε t A) (bdryTε o false (homs Θ))
    ∧ sameDown Θ (suppε u A) (bdryTε o true (homs Θ))

  -- The side condition of L_ε.
  graySideε : Ctx → Ty → Tm → Tm → Bool
  graySideε Θ A t u = cohCaseε Θ A t u ∨ opCaseε Θ A t u

------------------------------------------------------------------------
-- Constant orientations give L.

private
  cm-cong : ∀ {A B : Set} {f g : A → List B} → (∀ x → f x ≡ g x) → ∀ xs → concatMap f xs ≡ concatMap g xs
  cm-cong e []       = refl
  cm-cong e (x ∷ xs) = cong₂ _++_ (e x) (cm-cong e xs)

  not-not : ∀ b → not (not b) ≡ b
  not-not true  = refl
  not-not false = refl

  flip-not : ∀ i sg → (if odd i then not (not sg) else not sg) ≡ not (if odd i then not sg else sg)
  flip-not i sg with odd i
  ... | true  = refl
  ... | false = refl

chainε-false : ∀ sg k hs → chainε (λ _ → false) sg k hs ≡ chainT sg k hs
chainε-false sg k []       = refl
chainε-false sg k (h ∷ hs) =
  cm-cong (λ i → cong (prod1 (piece h i sg)) (chainε-false (if odd i then not sg else sg) (k ∸ i) hs))
          (filter (λ i → i <ℕ suc k) (upto k))

chainε-true : ∀ sg k hs → chainε (λ _ → true) sg k hs ≡ chainT (not sg) k hs
chainε-true sg k []       = refl
chainε-true sg k (h ∷ hs) =
  cm-cong (λ i → cong (prod1 (piece h i (not sg)))
                      (trans (chainε-true (if odd i then not sg else sg) (k ∸ i) hs)
                             (cong (λ b → chainT b (k ∸ i) hs) (sym (flip-not i sg)))))
          (filter (λ i → i <ℕ suc k) (upto k))

data ConstO : Orient → Set where
  c-false : ConstO (λ _ → false)
  c-true  : ConstO (λ _ → true)

chainTε-const : ∀ {o} → ConstO o → ∀ sg k hs → chainTε o sg k hs ≡ chainT sg k hs
chainTε-const c-false sg k hs = chainε-false sg k hs
chainTε-const c-true  sg k hs = trans (chainε-true (not sg) k hs) (cong (λ b → chainT b k hs) (not-not sg))

module _ {o} (c : ConstO o) where
  private
    lower≡ : ∀ m hs → lowerTε o m hs ≡ lowerT m hs
    lower≡ zero    hs = refl
    lower≡ (suc m) hs rewrite lower≡ m hs | chainTε-const c false m hs | chainTε-const c true m hs = refl

    full≡ : ∀ hs → fullTε o hs ≡ fullT hs
    full≡ hs rewrite lower≡ (dimK hs) hs | chainTε-const c true (dimK hs) hs = refl

    bdry≡ : ∀ sg hs → bdryTε o sg hs ≡ bdryT sg hs
    bdry≡ sg hs rewrite lower≡ (dimK hs ∸ 1) hs | chainTε-const c sg (dimK hs ∸ 1) hs = refl

  cohRel≡ : ∀ Θ A t u ρ → cohCaseε o Θ A t u ≡ cohCase Θ A t u → topsSubε o ρ ≡ topsSub ρ →
            topSε o (coh Θ (arr A t u) ρ) ≡ topS (coh Θ (arr A t u) ρ)
  cohRel≡ Θ A t u ρ e r rewrite e | r | chainTε-const c true (dimK (homs Θ)) (homs Θ) = refl

  mutual
    topSε≡ : ∀ t → topSε o t ≡ topS t
    topSε≡ (var v)               = refl
    topSε≡ (cst _)               = refl
    topSε≡ (coh Θ ⋆ ρ)           = refl
    topSε≡ (coh Θ (arr A t u) ρ) = cohRel≡ Θ A t u ρ (cohCaseε≡ Θ A t u) (topsSubε≡ ρ)

    topsSubε≡ : ∀ ρ → topsSubε o ρ ≡ topsSub ρ
    topsSubε≡ ⟨⟩       = refl
    topsSubε≡ (ρ ,ₛ t) = cong₂ (λ a b → a ++ (b ∷ [])) (topsSubε≡ ρ) (topSε≡ t)

    suppTyε≡ : ∀ A → suppTyε o A ≡ suppTy A
    suppTyε≡ ⋆                      = refl
    suppTyε≡ (arr ⋆ _ _)            = refl
    suppTyε≡ (arr (arr B s s') t u) =
      cong₂ _++_ (suppTyε≡ (arr B s s')) (cong₂ _++_ (topSε≡ t) (topSε≡ u))

    cohCaseε≡ : ∀ Θ A t u → cohCaseε o Θ A t u ≡ cohCase Θ A t u
    cohCaseε≡ Θ ⋆ t u = refl
    cohCaseε≡ Θ (arr B s s') t u =
      cong₂ (λ a b → endsOK Θ (arr B s s') ∧ sameDown Θ a (fullTε o (homs Θ)) ∧ sameDown Θ b (fullTε o (homs Θ)))
            (cong₂ _++_ (topSε≡ t) (suppTyε≡ (arr B s s')))
            (cong₂ _++_ (topSε≡ u) (suppTyε≡ (arr B s s')))
      ∙ cong (λ F → endsOK Θ (arr B s s') ∧ sameDown Θ (supp t (arr B s s')) F ∧ sameDown Θ (supp u (arr B s s')) F)
             (full≡ (homs Θ))
      where
      _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      _∙_ = trans

  suppε≡ : ∀ t A → suppε o t A ≡ supp t A
  suppε≡ t A = cong₂ _++_ (topSε≡ t) (suppTyε≡ A)

  opCaseε≡ : ∀ Θ A t u → opCaseε o Θ A t u ≡ opCase Θ A t u
  opCaseε≡ Θ ⋆ t u = refl
  opCaseε≡ Θ (arr B s s') t u
    rewrite suppε≡ t (arr B s s') | suppε≡ u (arr B s s') | bdry≡ false (homs Θ) | bdry≡ true (homs Θ) = refl

  -- L_ε = L for constant ε.
  graySideε-const : ∀ Θ A t u → graySideε o Θ A t u ≡ graySide Θ A t u
  graySideε-const Θ A t u rewrite cohCaseε≡ Θ A t u | opCaseε≡ Θ A t u = refl
