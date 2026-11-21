------------------------------------------------------------------------
-- An interchanger with an invertible input is invertible, given the
-- split law for that input (notes/uniform-marks.md, Lemma 4.4).
--
-- Setting. The data of one interchange position in a strict
-- ω-sesquicategory with directed interchangers (the T₁₂ signature of
-- spec chapter 2), cut down to what the argument uses:
--   * 1-cells f : x → y (type A1), g : y → z (type B1), their
--     composites x → z (type C1, written f · g);
--   * 2-cells between them, forming categories A2, B2, C2
--     (vertical composition _∗_, identities);
--   * whiskering of 2-cells by 1-cells, strictly functorial
--     (this is the sesquicategory axiom; no interchange law);
--   * 3-cells between parallel 2-cells of C2, forming a category C3
--     (composition _⨾_), whiskered on either side by 2-cells,
--     strictly functorial and strictly associative/unital
--     (again sesquicategory axioms, one dimension up);
--   * the interchanger
--        ι(F, G) : (f ◁ G) ∗ (F ▷ g′)  ⇛  (F ▷ g) ∗ (f′ ◁ G)
--     for F : f ⇒ f′ and G : g ⇒ g′.
-- Nothing here is postulated: the axioms are fields of a record, and
-- the theorems hold in every instance of the record.
--
-- Hypotheses of the two theorems (fields of `LeftSplit` / `RightSplit`):
--   unit law     ι(1_f, G) = 1     (resp. ι(F, 1_g) = 1),
--   split law    ι(F₁ ∗ F₂, G) = paste of ι(F₁, G) and ι(F₂, G)
--                (resp. the split of a composite right input).
-- In the kernel the split laws are the switches of spec §2.3: the
-- inner composite-crossing law is the left split, R the right split.
-- The unit law is one of the face and unit declarations of the
-- forced base B (lax r8 Response 1), so it holds in every setting.
--
-- Theorems.
--   left-inv  : F has a two-sided inverse ⇒ ι(F, G) has one (left split)
--   right-inv : G has a two-sided inverse ⇒ ι(F, G) has one (right split)
-- K is used (the library is --safe with K), only to transport along
-- equalities of 2-cells.
------------------------------------------------------------------------
module CaTTExp.Uniform.InnerInv where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Equality of cells up to equalities of their boundaries.

cast : ∀ {I : Set} (H : I → I → Set) {a a′ b b′ : I} →
       a ≡ a′ → b ≡ b′ → H a b → H a′ b′
cast H refl refl x = x

-- a ≅ b : a and b are equal once their source and target are
-- identified along equalities of indices.
data Het {I : Set} (H : I → I → Set) {a b : I} (x : H a b) :
         {a′ b′ : I} → H a′ b′ → Set where
  het : Het H x x

-- An isomorphism in a category given by hom-sets and composition.
record IsIso {O : Set} (H : O → O → Set)
             (_⨾_ : ∀ {a b c} → H a b → H b c → H a c)
             (idH : ∀ {a} → H a a) {a b : O} (t : H a b) : Set where
  field
    inv  : H b a
    linv : t ⨾ inv ≡ idH
    rinv : inv ⨾ t ≡ idH

------------------------------------------------------------------------
-- The structure.

record Slice : Set₁ where
  infixr 7 _·_
  infixr 6 _∗_ _∗A_ _∗B_
  infixr 5 _⨾_
  infix 4 _≅_
  field
    A1 B1 C1 : Set
    _·_ : A1 → B1 → C1

    -- 2-cells and vertical composition
    A2 : A1 → A1 → Set
    B2 : B1 → B1 → Set
    C2 : C1 → C1 → Set
    _∗A_ : ∀ {f f′ f″} → A2 f f′ → A2 f′ f″ → A2 f f″
    _∗B_ : ∀ {g g′ g″} → B2 g g′ → B2 g′ g″ → B2 g g″
    _∗_  : ∀ {u v w} → C2 u v → C2 v w → C2 u w
    1A : ∀ {f} → A2 f f
    1B : ∀ {g} → B2 g g
    1C : ∀ {u} → C2 u u
    ∗-assoc : ∀ {u v w t} (X : C2 u v) (Y : C2 v w) (Z : C2 w t) →
              (X ∗ Y) ∗ Z ≡ X ∗ (Y ∗ Z)
    ∗-idl : ∀ {u v} (X : C2 u v) → 1C ∗ X ≡ X
    ∗-idr : ∀ {u v} (X : C2 u v) → X ∗ 1C ≡ X

    -- whiskering 2-cells by 1-cells, strictly functorial
    _▷_ : ∀ {f f′} → A2 f f′ → (g : B1) → C2 (f · g) (f′ · g)
    _◁_ : ∀ (f : A1) {g g′} → B2 g g′ → C2 (f · g) (f · g′)
    ▷-∗ : ∀ {f f′ f″} (F : A2 f f′) (F′ : A2 f′ f″) g →
          (F ∗A F′) ▷ g ≡ (F ▷ g) ∗ (F′ ▷ g)
    ▷-1 : ∀ {f} g → (1A {f}) ▷ g ≡ 1C
    ◁-∗ : ∀ f {g g′ g″} (G : B2 g g′) (G′ : B2 g′ g″) →
          f ◁ (G ∗B G′) ≡ (f ◁ G) ∗ (f ◁ G′)
    ◁-1 : ∀ f {g} → f ◁ (1B {g}) ≡ 1C

    -- 3-cells between parallel 2-cells of C2
    C3 : ∀ {u v} → C2 u v → C2 u v → Set
    _⨾_ : ∀ {u v} {X Y Z : C2 u v} → C3 X Y → C3 Y Z → C3 X Z
    1₃  : ∀ {u v} {X : C2 u v} → C3 X X

  -- equality of 3-cells up to their boundaries
  _≅_ : ∀ {u v} {X Y X′ Y′ : C2 u v} → C3 X Y → C3 X′ Y′ → Set
  a ≅ b = Het C3 a b

  -- composition along an equality of the middle boundary
  _⨾⟨_⟩_ : ∀ {u v} {X Y Y′ Z : C2 u v} → C3 X Y → Y ≡ Y′ → C3 Y′ Z → C3 X Z
  a ⨾⟨ e ⟩ b = cast C3 refl e a ⨾ b

  field
    ⨾-idl : ∀ {u v} {X Y : C2 u v} (a : C3 X Y) → 1₃ ⨾ a ≡ a
    ⨾-idr : ∀ {u v} {X Y : C2 u v} (a : C3 X Y) → a ⨾ 1₃ ≡ a

    -- whiskering 3-cells by 2-cells (along 1-cells of the hom),
    -- strictly functorial, associative and unital
    lw : ∀ {u v w} (P : C2 u v) {X Y : C2 v w} → C3 X Y → C3 (P ∗ X) (P ∗ Y)
    rw : ∀ {u v w} {X Y : C2 u v} → C3 X Y → (Q : C2 v w) → C3 (X ∗ Q) (Y ∗ Q)
    lw-⨾ : ∀ {u v w} (P : C2 u v) {X Y Z : C2 v w} (a : C3 X Y) (b : C3 Y Z) →
           lw P (a ⨾ b) ≡ lw P a ⨾ lw P b
    rw-⨾ : ∀ {u v w} {X Y Z : C2 u v} (a : C3 X Y) (b : C3 Y Z) (Q : C2 v w) →
           rw (a ⨾ b) Q ≡ rw a Q ⨾ rw b Q
    lw-1 : ∀ {u v w} (P : C2 u v) {X : C2 v w} → lw P (1₃ {X = X}) ≡ 1₃
    rw-1 : ∀ {u v w} {X : C2 u v} (Q : C2 v w) → rw (1₃ {X = X}) Q ≡ 1₃
    lw-unit : ∀ {u v} {X Y : C2 u v} (a : C3 X Y) → lw 1C a ≅ a
    rw-unit : ∀ {u v} {X Y : C2 u v} (a : C3 X Y) → rw a 1C ≅ a
    lw-lw : ∀ {u v w t} (P : C2 u v) (P′ : C2 v w) {X Y : C2 w t} (a : C3 X Y) →
            lw P (lw P′ a) ≅ lw (P ∗ P′) a
    rw-rw : ∀ {u v w t} {X Y : C2 u v} (a : C3 X Y) (Q : C2 v w) (Q′ : C2 w t) →
            rw (rw a Q) Q′ ≅ rw a (Q ∗ Q′)
    lw-rw : ∀ {u v w t} (P : C2 u v) {X Y : C2 v w} (a : C3 X Y) (Q : C2 w t) →
            lw P (rw a Q) ≅ rw (lw P a) Q

    -- the interchanger, oriented as in spec §2.3 Example (a)
    ι : ∀ {f f′ g g′} (F : A2 f f′) (G : B2 g g′) →
        C3 ((f ◁ G) ∗ (F ▷ g′)) ((F ▷ g) ∗ (f′ ◁ G))

  InvA : ∀ {f f′} → A2 f f′ → Set
  InvA = IsIso A2 _∗A_ 1A
  InvB : ∀ {g g′} → B2 g g′ → Set
  InvB = IsIso B2 _∗B_ 1B
  Inv3 : ∀ {u v} {X Y : C2 u v} → C3 X Y → Set
  Inv3 t = IsIso C3 _⨾_ 1₃ t

------------------------------------------------------------------------
-- The two split laws and the unit laws, as hypotheses.

record LeftSplit (S : Slice) : Set where
  open Slice S
  field
    -- ι(1, G) is an identity
    unitL : ∀ {f g g′} (G : B2 g g′) → ι (1A {f}) G ≅ 1₃ {X = f ◁ G}
    -- inner composite-crossing law (left split):
    -- ι(F₁ ∗ F₂, G) = (ι(F₁, G) ▹ (F₂ ▷ g′)) ⨾ ((F₁ ▷ g) ◃ ι(F₂, G))
    splitL : ∀ {f f′ f″ g g′} (F₁ : A2 f f′) (F₂ : A2 f′ f″) (G : B2 g g′) →
             ι (F₁ ∗A F₂) G ≅
             (rw (ι F₁ G) (F₂ ▷ g′) ⨾⟨ ∗-assoc _ _ _ ⟩ lw (F₁ ▷ g) (ι F₂ G))

record RightSplit (S : Slice) : Set where
  open Slice S
  field
    unitR : ∀ {f f′ g} (F : A2 f f′) → ι F (1B {g}) ≅ 1₃ {X = F ▷ g}
    -- right split R:
    -- ι(F, G₁ ∗ G₂) = ((f ◁ G₁) ◃ ι(F, G₂)) ⨾ (ι(F, G₁) ▹ (f′ ◁ G₂))
    splitR : ∀ {f f′ g g′ g″} (F : A2 f f′) (G₁ : B2 g g′) (G₂ : B2 g′ g″) →
             ι F (G₁ ∗B G₂) ≅
             (lw (f ◁ G₁) (ι F G₂) ⨾⟨ sym (∗-assoc _ _ _) ⟩ rw (ι F G₁) (f′ ◁ G₂))

------------------------------------------------------------------------
-- Generic facts about Het (K is used through pattern matching).

module _ {I : Set} {H : I → I → Set} where
  het-sym : ∀ {a b a′ b′} {x : H a b} {y : H a′ b′} → Het H x y → Het H y x
  het-sym het = het

  het-trans : ∀ {a b a′ b′ a″ b″} {x : H a b} {y : H a′ b′} {z : H a″ b″} →
              Het H x y → Het H y z → Het H x z
  het-trans het q = q

  het-≡ : ∀ {a b} {x y : H a b} → Het H x y → x ≡ y
  het-≡ het = refl

  ≡-het : ∀ {a b} {x y : H a b} → x ≡ y → Het H x y
  ≡-het refl = het

  cast-het : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (x : H a b) → Het H (cast H p q x) x
  cast-het refl refl x = het

infixr 2 _≅⟨_⟩_ _≡⟨_⟩ₕ_
infix 3 _∎ₕ
_≅⟨_⟩_ : ∀ {I} {H : I → I → Set} {a b a′ b′ a″ b″} (x : H a b) {y : H a′ b′} {z : H a″ b″} →
         Het H x y → Het H y z → Het H x z
x ≅⟨ p ⟩ q = het-trans p q

_≡⟨_⟩ₕ_ : ∀ {I} {H : I → I → Set} {a b a″ b″} (x : H a b) {y : H a b} {z : H a″ b″} →
          x ≡ y → Het H y z → Het H x z
x ≡⟨ refl ⟩ₕ q = q

_∎ₕ : ∀ {I} {H : I → I → Set} {a b} (x : H a b) → Het H x x
x ∎ₕ = het

------------------------------------------------------------------------
-- Congruences in a slice.

module SliceFacts (S : Slice) where
  open Slice S

  ⨾-het : ∀ {u v} {X Y Z X′ Y′ Z′ : C2 u v}
          {a : C3 X Y} {b : C3 Y Z} {a′ : C3 X′ Y′} {b′ : C3 Y′ Z′} →
          a ≅ a′ → b ≅ b′ → (a ⨾ b) ≅ (a′ ⨾ b′)
  ⨾-het het het = het

  lw-het : ∀ {u v w} (P : C2 u v) {X Y X′ Y′ : C2 v w} {a : C3 X Y} {a′ : C3 X′ Y′} →
           a ≅ a′ → lw P a ≅ lw P a′
  lw-het P het = het

  rw-het : ∀ {u v w} {X Y X′ Y′ : C2 u v} {a : C3 X Y} {a′ : C3 X′ Y′} (Q : C2 v w) →
           a ≅ a′ → rw a Q ≅ rw a′ Q
  rw-het Q het = het

  lw-P : ∀ {u v w} {P P′ : C2 u v} {X Y : C2 v w} (a : C3 X Y) → P ≡ P′ → lw P a ≅ lw P′ a
  lw-P a refl = het

  rw-Q : ∀ {u v w} {X Y : C2 u v} (a : C3 X Y) {Q Q′ : C2 v w} → Q ≡ Q′ → rw a Q ≅ rw a Q′
  rw-Q a refl = het

  ι-F : ∀ {f f′ g g′} {F F′ : A2 f f′} (G : B2 g g′) → F ≡ F′ → ι F G ≅ ι F′ G
  ι-F G refl = het

  ι-G : ∀ {f f′ g g′} (F : A2 f f′) {G G′ : B2 g g′} → G ≡ G′ → ι F G ≅ ι F G′
  ι-G F refl = het

  -- a composite along an equality of middle boundaries is Het to the
  -- composite of anything Het to its pieces
  ⨾⟨⟩-het : ∀ {u v} {X Y Y₁ Z X′ Y′ Z′ : C2 u v} (a : C3 X Y) (e : Y ≡ Y₁) (b : C3 Y₁ Z)
            {a′ : C3 X′ Y′} {b′ : C3 Y′ Z′} → a ≅ a′ → b ≅ b′ → (a ⨾⟨ e ⟩ b) ≅ (a′ ⨾ b′)
  ⨾⟨⟩-het a e b p q = ⨾-het (het-trans (cast-het refl e a) p) q

  lw-⨾⟨⟩ : ∀ {u v w} (P : C2 u v) {X Y Y₁ Z : C2 v w} (a : C3 X Y) (e : Y ≡ Y₁) (b : C3 Y₁ Z) →
           lw P (a ⨾⟨ e ⟩ b) ≅ (lw P a ⨾⟨ cong (P ∗_) e ⟩ lw P b)
  lw-⨾⟨⟩ P a refl b = ≡-het (lw-⨾ P a b)

  rw-⨾⟨⟩ : ∀ {u v w} {X Y Y₁ Z : C2 u v} (a : C3 X Y) (e : Y ≡ Y₁) (b : C3 Y₁ Z) (Q : C2 v w) →
           rw (a ⨾⟨ e ⟩ b) Q ≅ (rw a Q ⨾⟨ cong (_∗ Q) e ⟩ rw b Q)
  rw-⨾⟨⟩ a refl b Q = ≡-het (rw-⨾ a b Q)

  -- equational helpers for 2-cells
  ▷-cancel : ∀ {f f′} {F : A2 f f′} {F′ : A2 f′ f} → F ∗A F′ ≡ 1A → ∀ g →
             (F ▷ g) ∗ (F′ ▷ g) ≡ 1C
  ▷-cancel {F = F} {F′} e g = trans (sym (▷-∗ F F′ g)) (trans (cong (_▷ g) e) (▷-1 g))

  ◁-cancel : ∀ f {g g′} {G : B2 g g′} {G′ : B2 g′ g} → G ∗B G′ ≡ 1B →
             (f ◁ G) ∗ (f ◁ G′) ≡ 1C
  ◁-cancel f {G = G} {G′} e = trans (sym (◁-∗ f G G′)) (trans (cong (f ◁_) e) (◁-1 f))

  -- (X ∗ Y) ∗ Z ≡ X when Y ∗ Z ≡ 1
  absorbR : ∀ {u v w} (X : C2 u v) {Y : C2 v w} {Z : C2 w v} → Y ∗ Z ≡ 1C → (X ∗ Y) ∗ Z ≡ X
  absorbR X {Y} {Z} e = trans (∗-assoc X Y Z) (trans (cong (X ∗_) e) (∗-idr X))

  -- X ∗ (Y ∗ Z) ≡ Z when X ∗ Y ≡ 1
  absorbL : ∀ {u v w} {X : C2 u v} {Y : C2 v u} (Z : C2 u w) → X ∗ Y ≡ 1C → X ∗ (Y ∗ Z) ≡ Z
  absorbL {X = X} {Y} Z e = trans (sym (∗-assoc X Y Z)) (trans (cong (_∗ Z) e) (∗-idl Z))

------------------------------------------------------------------------
-- Theorem (left): with the left split, an interchanger whose left
-- input is invertible is invertible.

module Left (S : Slice) (LS : LeftSplit S) where
  open Slice S
  open LeftSplit LS
  open SliceFacts S

  left-inv : ∀ {f f′ g g′} (F : A2 f f′) (G : B2 g g′) → InvA F → Inv3 (ι F G)
  left-inv {f} {f′} {g} {g′} F G iF = record { inv = ψ ; linv = het-≡ lin ; rinv = het-≡ rin }
    where
      open IsIso iF renaming (inv to F′; linv to e₁; rinv to e₂)
      P = ι F G
      Q = ι F′ G
      ψ₀ = lw (F ▷ g) (rw Q (F ▷ g′))
      srcEq : (F ▷ g) ∗ (((f′ ◁ G) ∗ (F′ ▷ g′)) ∗ (F ▷ g′)) ≡ (F ▷ g) ∗ (f′ ◁ G)
      srcEq = cong ((F ▷ g) ∗_) (absorbR (f′ ◁ G) (▷-cancel e₂ g′))
      tgtEq : (F ▷ g) ∗ (((F′ ▷ g) ∗ (f ◁ G)) ∗ (F ▷ g′)) ≡ (f ◁ G) ∗ (F ▷ g′)
      tgtEq = trans (cong ((F ▷ g) ∗_) (∗-assoc (F′ ▷ g) (f ◁ G) (F ▷ g′)))
                    (absorbL ((f ◁ G) ∗ (F ▷ g′)) (▷-cancel e₁ g))
      ψ = cast C3 srcEq tgtEq ψ₀

      -- P ⨾ ψ = 1 : whisker the split of ι(F ∗ F′, G) = ι(1, G) = 1 by F ▷ g′
      lin : (P ⨾ ψ) ≅ 1₃ {X = (f ◁ G) ∗ (F ▷ g′)}
      lin = het-sym (
        1₃
          ≡⟨ sym (rw-1 (F ▷ g′)) ⟩ₕ
        rw 1₃ (F ▷ g′)
          ≅⟨ rw-het (F ▷ g′) (het-sym (het-trans (ι-F G e₁) (unitL G))) ⟩
        rw (ι (F ∗A F′) G) (F ▷ g′)
          ≅⟨ rw-het (F ▷ g′) (splitL F F′ G) ⟩
        rw (rw P (F′ ▷ g′) ⨾⟨ ∗-assoc _ _ _ ⟩ lw (F ▷ g) Q) (F ▷ g′)
          ≅⟨ rw-⨾⟨⟩ (rw P (F′ ▷ g′)) (∗-assoc _ _ _) (lw (F ▷ g) Q) (F ▷ g′) ⟩
        (rw (rw P (F′ ▷ g′)) (F ▷ g′) ⨾⟨ _ ⟩ rw (lw (F ▷ g) Q) (F ▷ g′))
          ≅⟨ ⨾⟨⟩-het _ _ _
               (rw (rw P (F′ ▷ g′)) (F ▷ g′)
                  ≅⟨ rw-rw P (F′ ▷ g′) (F ▷ g′) ⟩
                rw P ((F′ ▷ g′) ∗ (F ▷ g′))
                  ≅⟨ rw-Q P (▷-cancel e₂ g′) ⟩
                rw P 1C
                  ≅⟨ rw-unit P ⟩
                P ∎ₕ)
               (rw (lw (F ▷ g) Q) (F ▷ g′)
                  ≅⟨ het-sym (lw-rw (F ▷ g) Q (F ▷ g′)) ⟩
                ψ₀
                  ≅⟨ het-sym (cast-het srcEq tgtEq ψ₀) ⟩
                ψ ∎ₕ) ⟩
        (P ⨾ ψ) ∎ₕ)

      -- ψ ⨾ P = 1 : left-whisker the split of ι(F′ ∗ F, G) = 1 by F ▷ g
      rin : (ψ ⨾ P) ≅ 1₃ {X = (F ▷ g) ∗ (f′ ◁ G)}
      rin = het-sym (
        1₃
          ≡⟨ sym (lw-1 (F ▷ g)) ⟩ₕ
        lw (F ▷ g) 1₃
          ≅⟨ lw-het (F ▷ g) (het-sym (het-trans (ι-F G e₂) (unitL G))) ⟩
        lw (F ▷ g) (ι (F′ ∗A F) G)
          ≅⟨ lw-het (F ▷ g) (splitL F′ F G) ⟩
        lw (F ▷ g) (rw Q (F ▷ g′) ⨾⟨ ∗-assoc _ _ _ ⟩ lw (F′ ▷ g) P)
          ≅⟨ lw-⨾⟨⟩ (F ▷ g) (rw Q (F ▷ g′)) (∗-assoc _ _ _) (lw (F′ ▷ g) P) ⟩
        (lw (F ▷ g) (rw Q (F ▷ g′)) ⨾⟨ _ ⟩ lw (F ▷ g) (lw (F′ ▷ g) P))
          ≅⟨ ⨾⟨⟩-het _ _ _
               (het-sym (cast-het srcEq tgtEq ψ₀))
               (lw (F ▷ g) (lw (F′ ▷ g) P)
                  ≅⟨ lw-lw (F ▷ g) (F′ ▷ g) P ⟩
                lw ((F ▷ g) ∗ (F′ ▷ g)) P
                  ≅⟨ lw-P P (▷-cancel e₁ g) ⟩
                lw 1C P
                  ≅⟨ lw-unit P ⟩
                P ∎ₕ) ⟩
        (ψ ⨾ P) ∎ₕ)

------------------------------------------------------------------------
-- Theorem (right): with the right split R, an interchanger whose right
-- input is invertible is invertible.

module Right (S : Slice) (RS : RightSplit S) where
  open Slice S
  open RightSplit RS
  open SliceFacts S

  right-inv : ∀ {f f′ g g′} (F : A2 f f′) (G : B2 g g′) → InvB G → Inv3 (ι F G)
  right-inv {f} {f′} {g} {g′} F G iG = record { inv = ψ ; linv = het-≡ lin ; rinv = het-≡ rin }
    where
      open IsIso iG renaming (inv to G′; linv to e₁; rinv to e₂)
      P = ι F G
      Q = ι F G′
      -- Q : (f ◁ G′) ∗ (F ▷ g) ⇛ (F ▷ g′) ∗ (f′ ◁ G′)
      ψ₀ = rw (lw (f ◁ G) Q) (f′ ◁ G)
      srcEq : ((f ◁ G) ∗ ((f ◁ G′) ∗ (F ▷ g))) ∗ (f′ ◁ G) ≡ (F ▷ g) ∗ (f′ ◁ G)
      srcEq = cong (_∗ (f′ ◁ G)) (absorbL (F ▷ g) (◁-cancel f e₁))
      tgtEq : ((f ◁ G) ∗ ((F ▷ g′) ∗ (f′ ◁ G′))) ∗ (f′ ◁ G) ≡ (f ◁ G) ∗ (F ▷ g′)
      tgtEq = trans (cong (_∗ (f′ ◁ G)) (sym (∗-assoc (f ◁ G) (F ▷ g′) (f′ ◁ G′))))
                    (absorbR ((f ◁ G) ∗ (F ▷ g′)) (◁-cancel f′ e₂))
      ψ = cast C3 srcEq tgtEq ψ₀

      -- ψ ⨾ P = 1 : right-whisker the split of ι(F, G ∗ G′) = 1 by f′ ◁ G
      rin : (ψ ⨾ P) ≅ 1₃ {X = (F ▷ g) ∗ (f′ ◁ G)}
      rin = het-sym (
        1₃
          ≡⟨ sym (rw-1 (f′ ◁ G)) ⟩ₕ
        rw 1₃ (f′ ◁ G)
          ≅⟨ rw-het (f′ ◁ G) (het-sym (het-trans (ι-G F e₁) (unitR F))) ⟩
        rw (ι F (G ∗B G′)) (f′ ◁ G)
          ≅⟨ rw-het (f′ ◁ G) (splitR F G G′) ⟩
        rw (lw (f ◁ G) Q ⨾⟨ sym (∗-assoc _ _ _) ⟩ rw P (f′ ◁ G′)) (f′ ◁ G)
          ≅⟨ rw-⨾⟨⟩ (lw (f ◁ G) Q) (sym (∗-assoc _ _ _)) (rw P (f′ ◁ G′)) (f′ ◁ G) ⟩
        (rw (lw (f ◁ G) Q) (f′ ◁ G) ⨾⟨ _ ⟩ rw (rw P (f′ ◁ G′)) (f′ ◁ G))
          ≅⟨ ⨾⟨⟩-het _ _ _
               (het-sym (cast-het srcEq tgtEq ψ₀))
               (rw (rw P (f′ ◁ G′)) (f′ ◁ G)
                  ≅⟨ rw-rw P (f′ ◁ G′) (f′ ◁ G) ⟩
                rw P ((f′ ◁ G′) ∗ (f′ ◁ G))
                  ≅⟨ rw-Q P (◁-cancel f′ e₂) ⟩
                rw P 1C
                  ≅⟨ rw-unit P ⟩
                P ∎ₕ) ⟩
        (ψ ⨾ P) ∎ₕ)

      -- P ⨾ ψ = 1 : left-whisker the split of ι(F, G′ ∗ G) = 1 by f ◁ G
      lin : (P ⨾ ψ) ≅ 1₃ {X = (f ◁ G) ∗ (F ▷ g′)}
      lin = het-sym (
        1₃
          ≡⟨ sym (lw-1 (f ◁ G)) ⟩ₕ
        lw (f ◁ G) 1₃
          ≅⟨ lw-het (f ◁ G) (het-sym (het-trans (ι-G F e₂) (unitR F))) ⟩
        lw (f ◁ G) (ι F (G′ ∗B G))
          ≅⟨ lw-het (f ◁ G) (splitR F G′ G) ⟩
        lw (f ◁ G) (lw (f ◁ G′) P ⨾⟨ sym (∗-assoc _ _ _) ⟩ rw Q (f′ ◁ G))
          ≅⟨ lw-⨾⟨⟩ (f ◁ G) (lw (f ◁ G′) P) (sym (∗-assoc _ _ _)) (rw Q (f′ ◁ G)) ⟩
        (lw (f ◁ G) (lw (f ◁ G′) P) ⨾⟨ _ ⟩ lw (f ◁ G) (rw Q (f′ ◁ G)))
          ≅⟨ ⨾⟨⟩-het _ _ _
               (lw (f ◁ G) (lw (f ◁ G′) P)
                  ≅⟨ lw-lw (f ◁ G) (f ◁ G′) P ⟩
                lw ((f ◁ G) ∗ (f ◁ G′)) P
                  ≅⟨ lw-P P (◁-cancel f e₁) ⟩
                lw 1C P
                  ≅⟨ lw-unit P ⟩
                P ∎ₕ)
               (lw (f ◁ G) (rw Q (f′ ◁ G))
                  ≅⟨ lw-rw (f ◁ G) Q (f′ ◁ G) ⟩
                ψ₀
                  ≅⟨ het-sym (cast-het srcEq tgtEq ψ₀) ⟩
                ψ ∎ₕ) ⟩
        (P ⨾ ψ) ∎ₕ)
