------------------------------------------------------------------------
-- The separating algebra M and the failure of the composite-crossing
-- law for the inner interchanger
-- (notes/conjectures/answered/lax-interchange-construction-or-
--  impossibility-2026-11-19.md, §7, (52)–(63)).
--
-- M has one cell in dimensions 0–2, 3-cells P = {0, 1, 2} under capped
-- addition, and 4-cells (m, S) with m ∈ P and a weight S ⊆ {1,2}².
-- All compositions take ⊕ on bases and ∪ on weights; χ ↦ 0, r and t
-- ↦ identities, and ι(m, n) has weight {(m, n)} when m, n > 0, else ∅.
--
-- Here:
--   * T3, T4: raw (untyped) terms for 3- and 4-cells of the theory T
--     over any signature of input generators;
--   * _≈3_, _≈_: the equations of T through dimension 4, as schemas on
--     raw terms. They comprise the sesquicategory laws, (7)–(9), the
--     eight naturality-composition equations (10)–(17), (18), the
--     restricted laws (20)–(21), the identity normalisations, and the
--     support equations. Raw terms include ill-typed instances, so
--     proving invariance for all of them covers the typed ones;
--   * val3, weight: the interpretation in M. A 4-cell's M-value is
--     (value of its source, weight); equations relate parallel cells,
--     so M satisfies an equation exactly when the weights agree;
--   * val3-≈, weight-≈: M satisfies every equation (soundness);
--   * composite-crossing-fails: (63), ι(A, B;C) ≠ the pairwise
--     composite, in the free algebra on the diagram of §7.2.
--
-- 1-whiskering (by 1-cells) is included as labelled unary operators;
-- 5-cells add no 4-dimensional equations and are not modelled.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Finite using (_∈L_; here; there)

module CaTTExp.Join.SepAlgebra where

------------------------------------------------------------------------
-- The algebra M.

data P3 : Set where
  p0 p1 p2 : P3

infixl 6 _⊕_
_⊕_ : P3 → P3 → P3
p0 ⊕ n  = n
p1 ⊕ p0 = p1
p1 ⊕ p1 = p2
p1 ⊕ p2 = p2
p2 ⊕ _  = p2

⊕-assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc p0 b  c  = refl
⊕-assoc p1 p0 c  = refl
⊕-assoc p1 p1 p0 = refl
⊕-assoc p1 p1 p1 = refl
⊕-assoc p1 p1 p2 = refl
⊕-assoc p1 p2 p0 = refl
⊕-assoc p1 p2 p1 = refl
⊕-assoc p1 p2 p2 = refl
⊕-assoc p2 b  c  = refl

⊕-idʳ : ∀ a → a ⊕ p0 ≡ a
⊕-idʳ p0 = refl
⊕-idʳ p1 = refl
⊕-idʳ p2 = refl

-- Weights: subsets of {1,2} × {1,2}.
record W : Set where
  constructor w
  field
    w11 w12 w21 w22 : Bool

∅ : W
∅ = w false false false false

infixl 5 _∪_
_∪_ : W → W → W
w a b c d ∪ w a′ b′ c′ d′ = w (a ∨ a′) (b ∨ b′) (c ∨ c′) (d ∨ d′)

private
  ∨-assoc : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

  ∨-false : ∀ a → a ∨ false ≡ a
  ∨-false true  = refl
  ∨-false false = refl

  ∨-comm : ∀ a b → a ∨ b ≡ b ∨ a
  ∨-comm true  true  = refl
  ∨-comm true  false = refl
  ∨-comm false true  = refl
  ∨-comm false false = refl

  ∨-idem : ∀ a → a ∨ a ≡ a
  ∨-idem true  = refl
  ∨-idem false = refl

  cong₄ : ∀ {a b c d a′ b′ c′ d′ : Bool} → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
          w a b c d ≡ w a′ b′ c′ d′
  cong₄ refl refl refl refl = refl

∪-assoc : ∀ x y z → (x ∪ y) ∪ z ≡ x ∪ (y ∪ z)
∪-assoc (w a b c d) (w a′ b′ c′ d′) (w a″ b″ c″ d″) =
  cong₄ (∨-assoc a a′ a″) (∨-assoc b b′ b″) (∨-assoc c c′ c″) (∨-assoc d d′ d″)

∪-idʳ : ∀ x → x ∪ ∅ ≡ x
∪-idʳ (w a b c d) = cong₄ (∨-false a) (∨-false b) (∨-false c) (∨-false d)

∪-comm : ∀ x y → x ∪ y ≡ y ∪ x
∪-comm (w a b c d) (w a′ b′ c′ d′) =
  cong₄ (∨-comm a a′) (∨-comm b b′) (∨-comm c c′) (∨-comm d d′)

∪-idem : ∀ x → x ∪ x ≡ x
∪-idem (w a b c d) = cong₄ (∨-idem a) (∨-idem b) (∨-idem c) (∨-idem d)

-- (56): the weight of ι(m, n).
tag : P3 → P3 → W
tag p1 p1 = w true false false false
tag p1 p2 = w false true false false
tag p2 p1 = w false false true false
tag p2 p2 = w false false false true
tag _  _  = ∅

tag-0ʳ : ∀ m → tag m p0 ≡ ∅
tag-0ʳ p0 = refl
tag-0ʳ p1 = refl
tag-0ʳ p2 = refl

tag-0ˡ : ∀ n → tag p0 n ≡ ∅
tag-0ˡ p0 = refl
tag-0ˡ p1 = refl
tag-0ˡ p2 = refl

------------------------------------------------------------------------
-- Raw terms of T through dimension 4.

module Theory (G1 G2 G3 G4 : Set) where

  -- 2-cells: generators, identities, composites along 1-cells, and
  -- 1-whiskerings f x, x g.
  data T2 : Set where
    gen2  : G2 → T2
    id2   : T2
    _∘₂_  : T2 → T2 → T2
    w1L₂  : G1 → T2 → T2
    w1R₂  : T2 → G1 → T2

  -- 3-cells.
  infixl 5 _⨾_
  data T3 : Set where
    gen3  : G3 → T3
    id3   : T2 → T3
    χ     : T2 → T2 → T3          -- χ(a, b) : ba ⇛ ab
    _⨾_   : T3 → T3 → T3          -- composition along 2-cells
    wl    : T2 → T3 → T3          -- x F
    wr    : T3 → T2 → T3          -- F y
    w1L₃  : G1 → T3 → T3
    w1R₃  : T3 → G1 → T3

  -- 4-cells.
  infixl 6 _·_
  data T4 : Set where
    gen4  : G4 → T4
    id4   : T3 → T4
    ι     : T3 → T3 → T4          -- ι(F, G)
    r     : T3 → T2 → T4          -- r(A, b)
    t     : T2 → T3 → T4          -- t(a, B)
    _·_   : T4 → T4 → T4          -- composition along 3-cells
    ctx   : T3 → T4 → T3 → T4     -- [p | Θ | q]
    wl4   : T2 → T4 → T4
    wr4   : T4 → T2 → T4
    w1L₄  : G1 → T4 → T4
    w1R₄  : T4 → G1 → T4

  ----------------------------------------------------------------------
  -- Equations through dimension 3.

  infix 3 _≈3_
  data _≈3_ : T3 → T3 → Set where
    rfl3   : ∀ {F} → F ≈3 F
    sym3   : ∀ {F G} → F ≈3 G → G ≈3 F
    trans3 : ∀ {F G H} → F ≈3 G → G ≈3 H → F ≈3 H
    -- congruence
    ⨾-cong : ∀ {F F′ G G′} → F ≈3 F′ → G ≈3 G′ → F ⨾ G ≈3 F′ ⨾ G′
    wl-cong : ∀ {F F′} z → F ≈3 F′ → wl z F ≈3 wl z F′
    wr-cong : ∀ {F F′} z → F ≈3 F′ → wr F z ≈3 wr F′ z
    w1L-cong : ∀ {F F′} f → F ≈3 F′ → w1L₃ f F ≈3 w1L₃ f F′
    w1R-cong : ∀ {F F′} g → F ≈3 F′ → w1R₃ F g ≈3 w1R₃ F′ g
    -- sesquicategory laws
    ⨾-assoc : ∀ F G H → (F ⨾ G) ⨾ H ≈3 F ⨾ (G ⨾ H)
    ⨾-idˡ   : ∀ u F → id3 u ⨾ F ≈3 F
    ⨾-idʳ   : ∀ u F → F ⨾ id3 u ≈3 F
    wl-⨾    : ∀ z F G → wl z (F ⨾ G) ≈3 wl z F ⨾ wl z G
    wr-⨾    : ∀ z F G → wr (F ⨾ G) z ≈3 wr F z ⨾ wr G z
    wl-id   : ∀ z u → wl z (id3 u) ≈3 id3 (z ∘₂ u)
    wr-id   : ∀ z u → wr (id3 u) z ≈3 id3 (u ∘₂ z)
    wl-wl   : ∀ z z′ F → wl z (wl z′ F) ≈3 wl (z ∘₂ z′) F
    wr-wr   : ∀ z z′ F → wr (wr F z′) z ≈3 wr F (z′ ∘₂ z)
    wl-wr   : ∀ z z′ F → wl z (wr F z′) ≈3 wr (wl z F) z′
    wl-id2  : ∀ F → wl id2 F ≈3 F
    wr-id2  : ∀ F → wr F id2 ≈3 F
    w1L-⨾   : ∀ f F G → w1L₃ f (F ⨾ G) ≈3 w1L₃ f F ⨾ w1L₃ f G
    w1R-⨾   : ∀ g F G → w1R₃ (F ⨾ G) g ≈3 w1R₃ F g ⨾ w1R₃ G g
    w1L-id  : ∀ f u → w1L₃ f (id3 u) ≈3 id3 (w1L₂ f u)
    w1R-id  : ∀ g u → w1R₃ (id3 u) g ≈3 id3 (w1R₂ u g)
    w1L-wl  : ∀ f z F → w1L₃ f (wl z F) ≈3 wl (w1L₂ f z) (w1L₃ f F)
    w1L-wr  : ∀ f z F → w1L₃ f (wr F z) ≈3 wr (w1L₃ f F) (w1L₂ f z)
    w1R-wl  : ∀ g z F → w1R₃ (wl z F) g ≈3 wl (w1R₂ z g) (w1R₃ F g)
    w1R-wr  : ∀ g z F → w1R₃ (wr F z) g ≈3 wr (w1R₃ F g) (w1R₂ z g)
    -- (7) outer composite crossing
    χ-∘ˡ    : ∀ a₁ a₂ b → χ (a₁ ∘₂ a₂) b ≈3 wr (χ a₁ b) a₂ ⨾ wl a₁ (χ a₂ b)
    χ-∘ʳ    : ∀ a b₁ b₂ → χ a (b₁ ∘₂ b₂) ≈3 wl b₁ (χ a b₂) ⨾ wr (χ a b₁) b₂
    -- (8) for χ
    χ-w1L   : ∀ f x y → χ (w1L₂ f x) y ≈3 w1L₃ f (χ x y)
    χ-w1M   : ∀ g x y → χ (w1R₂ x g) y ≈3 χ x (w1L₂ g y)
    χ-w1R   : ∀ h x y → w1R₃ (χ x y) h ≈3 χ x (w1R₂ y h)
    -- normalisation at identity inputs
    χ-idˡ   : ∀ b → χ id2 b ≈3 id3 b
    χ-idʳ   : ∀ a → χ a id2 ≈3 id3 a

  ----------------------------------------------------------------------
  -- Equations through dimension 4.

  -- A path of 4-cells composed along 3-cells.
  path : T4 → List T4 → T4
  path X []       = X
  path X (Y ∷ Ys) = X · path Y Ys

  infix 3 _≈_
  data _≈_ : T4 → T4 → Set where
    rfl   : ∀ {X} → X ≈ X
    sym≈  : ∀ {X Y} → X ≈ Y → Y ≈ X
    trans≈ : ∀ {X Y Z} → X ≈ Y → Y ≈ Z → X ≈ Z
    -- congruence
    id4-cong : ∀ {F F′} → F ≈3 F′ → id4 F ≈ id4 F′
    ι-cong   : ∀ {F F′ G G′} → F ≈3 F′ → G ≈3 G′ → ι F G ≈ ι F′ G′
    r-cong   : ∀ {A A′} b → A ≈3 A′ → r A b ≈ r A′ b
    t-cong   : ∀ {B B′} a → B ≈3 B′ → t a B ≈ t a B′
    ·-cong   : ∀ {X X′ Y Y′} → X ≈ X′ → Y ≈ Y′ → X · Y ≈ X′ · Y′
    ctx-cong : ∀ {p p′ X X′ q q′} → p ≈3 p′ → X ≈ X′ → q ≈3 q′ →
               ctx p X q ≈ ctx p′ X′ q′
    wl4-cong : ∀ {X X′} z → X ≈ X′ → wl4 z X ≈ wl4 z X′
    wr4-cong : ∀ {X X′} z → X ≈ X′ → wr4 X z ≈ wr4 X′ z
    w1L-cong : ∀ {X X′} f → X ≈ X′ → w1L₄ f X ≈ w1L₄ f X′
    w1R-cong : ∀ {X X′} g → X ≈ X′ → w1R₄ X g ≈ w1R₄ X′ g
    -- sesquicategory laws
    ·-assoc  : ∀ X Y Z → (X · Y) · Z ≈ X · (Y · Z)
    ·-idˡ    : ∀ F X → id4 F · X ≈ X
    ·-idʳ    : ∀ F X → X · id4 F ≈ X
    ctx-id   : ∀ u v X → ctx (id3 u) X (id3 v) ≈ X
    ctx-ctx  : ∀ p p′ X q′ q → ctx p (ctx p′ X q′) q ≈ ctx (p ⨾ p′) X (q′ ⨾ q)
    ctx-·    : ∀ p X Y q → ctx p (X · Y) q ≈ ctx p X q · ctx p Y q
    ctx-id4  : ∀ p F q → ctx p (id4 F) q ≈ id4 (p ⨾ F ⨾ q)
    wl4-·    : ∀ z X Y → wl4 z (X · Y) ≈ wl4 z X · wl4 z Y
    wr4-·    : ∀ z X Y → wr4 (X · Y) z ≈ wr4 X z · wr4 Y z
    wl4-ctx  : ∀ z p X q → wl4 z (ctx p X q) ≈ ctx (wl z p) (wl4 z X) (wl z q)
    wr4-ctx  : ∀ z p X q → wr4 (ctx p X q) z ≈ ctx (wr p z) (wr4 X z) (wr q z)
    wl4-id4  : ∀ z F → wl4 z (id4 F) ≈ id4 (wl z F)
    wr4-id4  : ∀ z F → wr4 (id4 F) z ≈ id4 (wr F z)
    wl4-wl4  : ∀ z z′ X → wl4 z (wl4 z′ X) ≈ wl4 (z ∘₂ z′) X
    wr4-wr4  : ∀ z z′ X → wr4 (wr4 X z′) z ≈ wr4 X (z′ ∘₂ z)
    wl4-wr4  : ∀ z z′ X → wl4 z (wr4 X z′) ≈ wr4 (wl4 z X) z′
    wl4-id2  : ∀ X → wl4 id2 X ≈ X
    wr4-id2  : ∀ X → wr4 X id2 ≈ X
    w1L-·    : ∀ f X Y → w1L₄ f (X · Y) ≈ w1L₄ f X · w1L₄ f Y
    w1R-·    : ∀ g X Y → w1R₄ (X · Y) g ≈ w1R₄ X g · w1R₄ Y g
    w1L-ctx  : ∀ f p X q → w1L₄ f (ctx p X q) ≈ ctx (w1L₃ f p) (w1L₄ f X) (w1L₃ f q)
    w1R-ctx  : ∀ g p X q → w1R₄ (ctx p X q) g ≈ ctx (w1R₃ p g) (w1R₄ X g) (w1R₃ q g)
    w1L-id4  : ∀ f F → w1L₄ f (id4 F) ≈ id4 (w1L₃ f F)
    w1R-id4  : ∀ g F → w1R₄ (id4 F) g ≈ id4 (w1R₃ F g)
    w1L-wl4  : ∀ f z X → w1L₄ f (wl4 z X) ≈ wl4 (w1L₂ f z) (w1L₄ f X)
    w1L-wr4  : ∀ f z X → w1L₄ f (wr4 X z) ≈ wr4 (w1L₄ f X) (w1L₂ f z)
    w1R-wl4  : ∀ g z X → w1R₄ (wl4 z X) g ≈ wl4 (w1R₂ z g) (w1R₄ X g)
    w1R-wr4  : ∀ g z X → w1R₄ (wr4 X z) g ≈ wr4 (w1R₄ X g) (w1R₂ z g)
    -- (8) for r and t; 1-whiskering preserves ι
    r-w1L    : ∀ f A y → r (w1L₃ f A) y ≈ w1L₄ f (r A y)
    r-w1M    : ∀ g A y → r (w1R₃ A g) y ≈ r A (w1L₂ g y)
    r-w1R    : ∀ h A y → w1R₄ (r A y) h ≈ r A (w1R₂ y h)
    t-w1L    : ∀ f x B → t (w1L₂ f x) B ≈ w1L₄ f (t x B)
    t-w1M    : ∀ g x B → t (w1R₂ x g) B ≈ t x (w1L₃ g B)
    t-w1R    : ∀ h x B → w1R₄ (t x B) h ≈ t x (w1R₃ B h)
    ι-w1L    : ∀ f F G → ι (w1L₃ f F) (w1L₃ f G) ≈ w1L₄ f (ι F G)
    ι-w1R    : ∀ g F G → ι (w1R₃ F g) (w1R₃ G g) ≈ w1R₄ (ι F G) g
    -- (9) balancing for 2-whiskering
    ι-wl     : ∀ z F G → ι (wl z F) G ≈ wl4 z (ι F G)
    ι-wm     : ∀ z F G → ι (wr F z) G ≈ ι F (wl z G)
    ι-wr     : ∀ z F G → wr4 (ι F G) z ≈ ι F (wr G z)
    -- (10)–(13): composition of either argument of r, t
    r-⨾      : ∀ A A′ b e e′ → r (A ⨾ A′) b ≈
               ctx (id3 e) (r A b) (wr A′ b) · ctx (wl b A) (r A′ b) (id3 e′)
    t-⨾      : ∀ a B B′ e e′ → t a (B ⨾ B′) ≈
               ctx (wr B a) (t a B′) (id3 e) · ctx (id3 e′) (t a B) (wl a B′)
    r-∘      : ∀ A a a′ b₁ b₂ e e′ → r A (b₁ ∘₂ b₂) ≈
               ctx (wl b₁ (χ a b₂)) (wr4 (r A b₁) b₂) (id3 e) ·
               ctx (id3 e′) (wl4 b₁ (r A b₂)) (wr (χ a′ b₁) b₂)
    t-∘      : ∀ a₁ a₂ B b b′ e e′ → t (a₁ ∘₂ a₂) B ≈
               ctx (id3 e) (wr4 (t a₁ B) a₂) (wl a₁ (χ a₂ b′)) ·
               ctx (wr (χ a₁ b) a₂) (wl4 a₁ (t a₂ B)) (id3 e′)
    -- (14)–(17): whiskering of the varying argument
    r-wr     : ∀ A a a′ a₂ b e e′ → r (wr A a₂) b ≈
               ctx (wr (χ a b) a₂) (ι A (χ a₂ b)) (id3 e) ·
               ctx (id3 e′) (wr4 (r A b) a₂) (wl a′ (χ a₂ b))
    r-wl     : ∀ A a a′ a₁ b e e′ →                         -- (15)
               r (wl a₁ A) b · ctx (id3 e) (ι (χ a₁ b) A) (wl a₁ (χ a′ b)) ≈
               ctx (wr (χ a₁ b) a) (wl4 a₁ (r A b)) (id3 e′)
    t-wr     : ∀ B a b b′ b₂ e e′ →                         -- (16)
               ctx (id3 e) (ι B (χ a b₂)) (wr (χ a b′) b₂) · t a (wr B b₂) ≈
               ctx (wl b (χ a b₂)) (wr4 (t a B) b₂) (id3 e′)
    t-wl     : ∀ B a b b′ b₁ e e′ → t a (wl b₁ B) ≈          -- (17)
               ctx (id3 e) (wl4 b₁ (t a B)) (wr (χ a b₁) b′) ·
               ctx (wl b₁ (χ a b)) (ι (χ a b₁) B) (id3 e′)
    -- (18)
    τ-eq     : ∀ a b d → r (χ a b) d ≈ t a (χ b d)
    -- (20)–(21), with the literal χ argument
    ι-⨾ˡ     : ∀ F F′ a b v v′ e e′ → ι (F ⨾ F′) (χ a b) ≈
               ctx (id3 e) (ι F (χ a b)) (wr F′ v′) · ctx (wr F v) (ι F′ (χ a b)) (id3 e′)
    ι-⨾ʳ     : ∀ G G′ a b u u′ e e′ → ι (χ a b) (G ⨾ G′) ≈
               ctx (wl u G) (ι (χ a b) G′) (id3 e) · ctx (id3 e′) (ι (χ a b) G) (wl u′ G′)
    -- normalisation at identity inputs
    ι-idˡ    : ∀ u G F → ι (id3 u) G ≈ id4 F
    ι-idʳ    : ∀ u F H → ι F (id3 u) ≈ id4 H
    r-idˡ    : ∀ u b F → r (id3 u) b ≈ id4 F
    r-idʳ    : ∀ A F → r A id2 ≈ id4 F
    t-idˡ    : ∀ B F → t id2 B ≈ id4 F
    t-idʳ    : ∀ a u F → t a (id3 u) ≈ id4 F
    -- support equations: paths of edges with the same edge set
    supp     : ∀ X Xs Y Ys → (∀ {Z} → Z ∈L (X ∷ Xs) → Z ∈L (Y ∷ Ys)) →
               (∀ {Z} → Z ∈L (Y ∷ Ys) → Z ∈L (X ∷ Xs)) →
               path X Xs ≈ path Y Ys

  ----------------------------------------------------------------------
  -- The interpretation in M, for any values of the input 3-cells.

  module Interp (v3 : G3 → P3) where

    val3 : T3 → P3
    val3 (gen3 g)   = v3 g
    val3 (id3 _)    = p0
    val3 (χ _ _)    = p0
    val3 (F ⨾ G)    = val3 F ⊕ val3 G
    val3 (wl _ F)   = val3 F
    val3 (wr F _)   = val3 F
    val3 (w1L₃ _ F) = val3 F
    val3 (w1R₃ F _) = val3 F

    -- The weight of a 4-cell; its base is the value of its source.
    weight : T4 → W
    weight (gen4 _)   = ∅
    weight (id4 _)    = ∅
    weight (ι F G)    = tag (val3 F) (val3 G)
    weight (r _ _)    = ∅
    weight (t _ _)    = ∅
    weight (X · Y)    = weight X ∪ weight Y
    weight (ctx _ X _) = weight X
    weight (wl4 _ X)  = weight X
    weight (wr4 X _)  = weight X
    weight (w1L₄ _ X) = weight X
    weight (w1R₄ X _) = weight X

    -- M satisfies every 3-equation.
    val3-≈ : ∀ {F G} → F ≈3 G → val3 F ≡ val3 G
    val3-≈ rfl3            = refl
    val3-≈ (sym3 e)        = sym (val3-≈ e)
    val3-≈ (trans3 e f)    = trans (val3-≈ e) (val3-≈ f)
    val3-≈ (⨾-cong e f)    = cong₂ _⊕_ (val3-≈ e) (val3-≈ f)
    val3-≈ (wl-cong z e)   = val3-≈ e
    val3-≈ (wr-cong z e)   = val3-≈ e
    val3-≈ (w1L-cong f e)  = val3-≈ e
    val3-≈ (w1R-cong g e)  = val3-≈ e
    val3-≈ (⨾-assoc F G H) = ⊕-assoc (val3 F) (val3 G) (val3 H)
    val3-≈ (⨾-idˡ u F)     = refl
    val3-≈ (⨾-idʳ u F)     = ⊕-idʳ (val3 F)
    val3-≈ (wl-⨾ z F G)    = refl
    val3-≈ (wr-⨾ z F G)    = refl
    val3-≈ (wl-id z u)     = refl
    val3-≈ (wr-id z u)     = refl
    val3-≈ (wl-wl z z′ F)  = refl
    val3-≈ (wr-wr z z′ F)  = refl
    val3-≈ (wl-wr z z′ F)  = refl
    val3-≈ (wl-id2 F)      = refl
    val3-≈ (wr-id2 F)      = refl
    val3-≈ (w1L-⨾ f F G)   = refl
    val3-≈ (w1R-⨾ g F G)   = refl
    val3-≈ (w1L-id f u)    = refl
    val3-≈ (w1R-id g u)    = refl
    val3-≈ (w1L-wl f z F)  = refl
    val3-≈ (w1L-wr f z F)  = refl
    val3-≈ (w1R-wl g z F)  = refl
    val3-≈ (w1R-wr g z F)  = refl
    val3-≈ (χ-∘ˡ a₁ a₂ b)  = refl
    val3-≈ (χ-∘ʳ a b₁ b₂)  = refl
    val3-≈ (χ-w1L f x y)   = refl
    val3-≈ (χ-w1M g x y)   = refl
    val3-≈ (χ-w1R h x y)   = refl
    val3-≈ (χ-idˡ b)       = refl
    val3-≈ (χ-idʳ a)       = refl

    private
      pathW : T4 → List T4 → W
      pathW X Xs = weight (path X Xs)

      -- Each edge's weight lies below the path's.
      _⊆_ : W → W → Set
      x ⊆ y = x ∪ y ≡ y

      ⊆-∪ˡ : ∀ x y → x ⊆ (x ∪ y)
      ⊆-∪ˡ x y = trans (sym (∪-assoc x x y)) (cong (_∪ y) (∪-idem x))

      ⊆-∪ʳ : ∀ x y → y ⊆ (x ∪ y)
      ⊆-∪ʳ x y = trans (sym (∪-assoc y x y))
                 (trans (cong (_∪ y) (∪-comm y x))
                 (trans (∪-assoc x y y) (cong (x ∪_) (∪-idem y))))

      ⊆-trans : ∀ {x y z} → x ⊆ y → y ⊆ z → x ⊆ z
      ⊆-trans {x} {y} {z} p q =
        trans (cong (x ∪_) (sym q)) (trans (sym (∪-assoc x y z)) (trans (cong (_∪ z) p) q))

      ⊆-glb : ∀ {x y z} → x ⊆ z → y ⊆ z → (x ∪ y) ⊆ z
      ⊆-glb {x} {y} {z} p q = trans (∪-assoc x y z) (trans (cong (x ∪_) q) p)

      ⊆-antisym : ∀ {x y} → x ⊆ y → y ⊆ x → x ≡ y
      ⊆-antisym {x} {y} p q = trans (sym q) (trans (∪-comm y x) p)

      ∈-⊆ : ∀ {Z} X Xs → Z ∈L (X ∷ Xs) → weight Z ⊆ pathW X Xs
      ∈-⊆ X []       here      = ∪-idem (weight X)
      ∈-⊆ X (Y ∷ Ys) here      = ⊆-∪ˡ (weight X) (pathW Y Ys)
      ∈-⊆ X (Y ∷ Ys) (there m) = ⊆-trans (∈-⊆ Y Ys m) (⊆-∪ʳ (weight X) (pathW Y Ys))
      ∈-⊆ X []       (there ())

      sub-⊆ : ∀ X Xs Y Ys → (∀ {Z} → Z ∈L (X ∷ Xs) → Z ∈L (Y ∷ Ys)) →
              pathW X Xs ⊆ pathW Y Ys
      sub-⊆ X []       Y Ys s = ∈-⊆ Y Ys (s here)
      sub-⊆ X (X′ ∷ Xs) Y Ys s =
        ⊆-glb (∈-⊆ Y Ys (s here)) (sub-⊆ X′ Xs Y Ys (λ m → s (there m)))

    -- M satisfies every 4-equation of T.
    weight-≈ : ∀ {X Y} → X ≈ Y → weight X ≡ weight Y
    weight-≈ rfl                 = refl
    weight-≈ (sym≈ e)            = sym (weight-≈ e)
    weight-≈ (trans≈ e f)        = trans (weight-≈ e) (weight-≈ f)
    weight-≈ (id4-cong e)        = refl
    weight-≈ (ι-cong e f)        = cong₂ tag (val3-≈ e) (val3-≈ f)
    weight-≈ (r-cong b e)        = refl
    weight-≈ (t-cong a e)        = refl
    weight-≈ (·-cong e f)        = cong₂ _∪_ (weight-≈ e) (weight-≈ f)
    weight-≈ (ctx-cong e f g)    = weight-≈ f
    weight-≈ (wl4-cong z e)      = weight-≈ e
    weight-≈ (wr4-cong z e)      = weight-≈ e
    weight-≈ (w1L-cong f e)      = weight-≈ e
    weight-≈ (w1R-cong g e)      = weight-≈ e
    weight-≈ (·-assoc X Y Z)     = ∪-assoc (weight X) (weight Y) (weight Z)
    weight-≈ (·-idˡ F X)         = refl
    weight-≈ (·-idʳ F X)         = ∪-idʳ (weight X)
    weight-≈ (ctx-id u v X)      = refl
    weight-≈ (ctx-ctx p p′ X q′ q) = refl
    weight-≈ (ctx-· p X Y q)     = refl
    weight-≈ (ctx-id4 p F q)     = refl
    weight-≈ (wl4-· z X Y)       = refl
    weight-≈ (wr4-· z X Y)       = refl
    weight-≈ (wl4-ctx z p X q)   = refl
    weight-≈ (wr4-ctx z p X q)   = refl
    weight-≈ (wl4-id4 z F)       = refl
    weight-≈ (wr4-id4 z F)       = refl
    weight-≈ (wl4-wl4 z z′ X)    = refl
    weight-≈ (wr4-wr4 z z′ X)    = refl
    weight-≈ (wl4-wr4 z z′ X)    = refl
    weight-≈ (wl4-id2 X)         = refl
    weight-≈ (wr4-id2 X)         = refl
    weight-≈ (w1L-· f X Y)       = refl
    weight-≈ (w1R-· g X Y)       = refl
    weight-≈ (w1L-ctx f p X q)   = refl
    weight-≈ (w1R-ctx g p X q)   = refl
    weight-≈ (w1L-id4 f F)       = refl
    weight-≈ (w1R-id4 g F)       = refl
    weight-≈ (w1L-wl4 f z X)     = refl
    weight-≈ (w1L-wr4 f z X)     = refl
    weight-≈ (w1R-wl4 g z X)     = refl
    weight-≈ (w1R-wr4 g z X)     = refl
    weight-≈ (r-w1L f A y)       = refl
    weight-≈ (r-w1M g A y)       = refl
    weight-≈ (r-w1R h A y)       = refl
    weight-≈ (t-w1L f x B)       = refl
    weight-≈ (t-w1M g x B)       = refl
    weight-≈ (t-w1R h x B)       = refl
    weight-≈ (ι-w1L f F G)       = refl
    weight-≈ (ι-w1R g F G)       = refl
    weight-≈ (ι-wl z F G)        = refl
    weight-≈ (ι-wm z F G)        = refl
    weight-≈ (ι-wr z F G)        = refl
    weight-≈ (r-⨾ A A′ b e e′)   = refl
    weight-≈ (t-⨾ a B B′ e e′)   = refl
    weight-≈ (r-∘ A a a′ b₁ b₂ e e′) = refl
    weight-≈ (t-∘ a₁ a₂ B b b′ e e′) = refl
    weight-≈ (r-wr A a a′ a₂ b e e′) = sym (trans (∪-idʳ _) (tag-0ʳ (val3 A)))
    weight-≈ (r-wl A a a′ a₁ b e e′) = tag-0ˡ (val3 A)
    weight-≈ (t-wr B a b b′ b₂ e e′) = trans (∪-idʳ _) (tag-0ʳ (val3 B))
    weight-≈ (t-wl B a b b′ b₁ e e′) = sym (tag-0ˡ (val3 B))
    weight-≈ (τ-eq a b d)        = refl
    weight-≈ (ι-⨾ˡ F F′ a b v v′ e e′) =
      trans (tag-0ʳ (val3 F ⊕ val3 F′))
            (sym (cong₂ _∪_ (tag-0ʳ (val3 F)) (tag-0ʳ (val3 F′))))
    weight-≈ (ι-⨾ʳ G G′ a b u u′ e e′) =
      trans (tag-0ˡ (val3 G ⊕ val3 G′))
            (sym (cong₂ _∪_ (tag-0ˡ (val3 G′)) (tag-0ˡ (val3 G))))
    weight-≈ (ι-idˡ u G F)       = tag-0ˡ (val3 G)
    weight-≈ (ι-idʳ u F H)       = tag-0ʳ (val3 F)
    weight-≈ (r-idˡ u b F)       = refl
    weight-≈ (r-idʳ A F)         = refl
    weight-≈ (t-idˡ B F)         = refl
    weight-≈ (t-idʳ a u F)       = refl
    weight-≈ (supp X Xs Y Ys s s′) = ⊆-antisym (sub-⊆ X Xs Y Ys s) (sub-⊆ Y Ys X Xs s′)

------------------------------------------------------------------------
-- §7.2: two 0-cells, three 1-cells f₀ f₁ f₂, 2-cells α₀ α₁ : f₀ ⇒ f₁
-- and β₀ β₁ β₂ : f₁ ⇒ f₂, input 3-cells A : α₀ ⇛ α₁, B : β₀ ⇛ β₁,
-- C : β₁ ⇛ β₂, no input 4-cells.

data One : Set where
  f₀ f₁ f₂ : One

data Two : Set where
  α₀ α₁ β₀ β₁ β₂ : Two

data Three : Set where
  A B C : Three

open Theory One Two Three ⊥

-- (60): A, B, C ↦ 1.
open Interp (λ _ → p1)

-- (58) and (59).
D P : T4
D = ι (gen3 A) (gen3 B ⨾ gen3 C)
P = ctx (wl (gen2 α₀) (gen3 B)) (ι (gen3 A) (gen3 C)) (id3 (gen2 β₂)) ·
    ctx (id3 (gen2 β₀)) (ι (gen3 A) (gen3 B)) (wl (gen2 α₁) (gen3 C))

-- (61), (62).
weight-D : weight D ≡ w false true false false
weight-D = refl

weight-P : weight P ≡ w true false false false
weight-P = refl

-- (63): the composite-crossing law fails in the free algebra.
composite-crossing-fails : ¬ (D ≈ P)
composite-crossing-fails e with weight-≈ e
... | ()
