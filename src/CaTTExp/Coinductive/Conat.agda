------------------------------------------------------------------------
-- Ledger F12c, route 5 (notes/coinductive.md §4).
--
-- The conatural numbers without universal coproducts.  In any
-- cartesian closed category with finite coproducts, equalisers and a
-- natural numbers object, the object of decreasing sequences
--   M ↪ 2^ℕ,  the equaliser of  u ↦ u ∘ s  and  u ↦ u ∧ (u ∘ s),
-- with the structure map
--   out := cases(ι₁ ∘ !, ι₂ ∘ π₂) ∘ ⟨head, pred⟩ : M → 1 + M,
-- is a terminal coalgebra of X ↦ 1 + X.  Coproducts are NOT assumed
-- universal or disjoint: every case analysis is on a coproduct that is
-- a factor of an input, which distributivity (a consequence of
-- cartesian closure) handles (`case`, `cases`).
--
-- Setting: the record `CCC` below, a category with strict (≡)
-- equations of morphisms, a terminal object, binary products,
-- exponentials, binary coproducts, equalisers and an NNO with
-- uniqueness.  All are hypotheses of the module; no postulates.
--
-- Proved:
--   corec-mor   for every coalgebra c : C → 1 + C, a coalgebra
--               morphism C → M;
--   corec-uni   every coalgebra morphism C → M is equal to it.
--
-- Scope and honesty notes.
--   * 1-categorical with strict equality of morphisms: the 1-truncated
--     shadow.  Higher cells are not encoded.
--   * The setting is a cartesian closed category (⊗ = ×).  In the
--     system this is supplied by L-× at set targets; that translation,
--     and the h-levels of 2, 2^ℕ and 2^C it needs, are argued in the
--     notes, not encoded.  The non-cartesian (directed) case is not
--     covered.
--   * Finitely many constructors with arities (notes §4 route 5,
--     generalisation) are not encoded; only X ↦ 1 + X.
------------------------------------------------------------------------
module CaTTExp.Coinductive.Conat where

open import CaTTExp.Prelude using (_≡_; refl; sym; trans; cong; cong₂)
open import CaTTExp.Descent.CocartLemmas using (_≡⟨_⟩_; _∎)

record CCC : Set₁ where
  infixr 9 _∘_
  infixr 5 _×_
  infixr 4 _+_
  field
    Ob    : Set
    Hom   : Ob → Ob → Set
    id    : ∀ {A} → Hom A A
    _∘_   : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    idl   : ∀ {A B} (f : Hom A B) → id ∘ f ≡ f
    idr   : ∀ {A B} (f : Hom A B) → f ∘ id ≡ f
    assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
            (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

    𝟙     : Ob
    !     : ∀ {A} → Hom A 𝟙
    !-uni : ∀ {A} (f : Hom A 𝟙) → f ≡ !

    _×_   : Ob → Ob → Ob
    π₁    : ∀ {A B} → Hom (A × B) A
    π₂    : ∀ {A B} → Hom (A × B) B
    ⟨_,_⟩ : ∀ {W A B} → Hom W A → Hom W B → Hom W (A × B)
    π₁-β  : ∀ {W A B} (f : Hom W A) (g : Hom W B) → π₁ ∘ ⟨ f , g ⟩ ≡ f
    π₂-β  : ∀ {W A B} (f : Hom W A) (g : Hom W B) → π₂ ∘ ⟨ f , g ⟩ ≡ g
    ⟨⟩-η  : ∀ {W A B} (h : Hom W (A × B)) → ⟨ π₁ ∘ h , π₂ ∘ h ⟩ ≡ h

    Exp   : Ob → Ob → Ob        -- Exp A B = B^A
    ev    : ∀ {A B} → Hom (Exp A B × A) B
    lam   : ∀ {W A B} → Hom (W × A) B → Hom W (Exp A B)
    lam-β : ∀ {W A B} (f : Hom (W × A) B) → ev ∘ ⟨ lam f ∘ π₁ , π₂ ⟩ ≡ f
    lam-η : ∀ {W A B} (g : Hom W (Exp A B)) → lam (ev ∘ ⟨ g ∘ π₁ , π₂ ⟩) ≡ g

    _+_   : Ob → Ob → Ob
    ι₁    : ∀ {A B} → Hom A (A + B)
    ι₂    : ∀ {A B} → Hom B (A + B)
    [_,_] : ∀ {A B Y} → Hom A Y → Hom B Y → Hom (A + B) Y
    ι₁-β  : ∀ {A B Y} (f : Hom A Y) (g : Hom B Y) → [ f , g ] ∘ ι₁ ≡ f
    ι₂-β  : ∀ {A B Y} (f : Hom A Y) (g : Hom B Y) → [ f , g ] ∘ ι₂ ≡ g
    []-η  : ∀ {A B Y} (h : Hom (A + B) Y) → [ h ∘ ι₁ , h ∘ ι₂ ] ≡ h

    Eq      : ∀ {A B} → Hom A B → Hom A B → Ob
    eqm     : ∀ {A B} {f g : Hom A B} → Hom (Eq f g) A
    eqm-eq  : ∀ {A B} {f g : Hom A B} → f ∘ eqm {f = f} {g} ≡ g ∘ eqm
    fact    : ∀ {W A B} {f g : Hom A B} (k : Hom W A) → f ∘ k ≡ g ∘ k → Hom W (Eq f g)
    fact-β  : ∀ {W A B} {f g : Hom A B} (k : Hom W A) (p : f ∘ k ≡ g ∘ k) →
              eqm ∘ fact {f = f} {g} k p ≡ k
    eqm-mono : ∀ {W A B} {f g : Hom A B} (h h′ : Hom W (Eq f g)) →
               eqm ∘ h ≡ eqm ∘ h′ → h ≡ h′

    N     : Ob
    zero  : Hom 𝟙 N
    suc   : Hom N N
    it    : ∀ {Y} → Hom 𝟙 Y → Hom Y Y → Hom N Y
    it-z  : ∀ {Y} (x : Hom 𝟙 Y) (t : Hom Y Y) → it x t ∘ zero ≡ x
    it-s  : ∀ {Y} (x : Hom 𝟙 Y) (t : Hom Y Y) → it x t ∘ suc ≡ t ∘ it x t
    it-uni : ∀ {Y} (x : Hom 𝟙 Y) (t : Hom Y Y) (h : Hom N Y) →
             h ∘ zero ≡ x → h ∘ suc ≡ t ∘ h → h ≡ it x t

module Theory (𝒞 : CCC) where
  open CCC 𝒞

  ----------------------------------------------------------------------
  -- Basic reasoning

  ∘l : ∀ {A B C} {g g′ : Hom B C} (f : Hom A B) → g ≡ g′ → g ∘ f ≡ g′ ∘ f
  ∘l f refl = refl

  ∘r : ∀ {A B C} (g : Hom B C) {f f′ : Hom A B} → f ≡ f′ → g ∘ f ≡ g ∘ f′
  ∘r g refl = refl

  pair≡ : ∀ {W A B} {f f′ : Hom W A} {g g′ : Hom W B} →
          f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩
  pair≡ refl refl = refl

  ⟨⟩-∘ : ∀ {V W A B} (f : Hom W A) (g : Hom W B) (h : Hom V W) →
         ⟨ f , g ⟩ ∘ h ≡ ⟨ f ∘ h , g ∘ h ⟩
  ⟨⟩-∘ f g h =
    ⟨ f , g ⟩ ∘ h
      ≡⟨ sym (⟨⟩-η _) ⟩
    ⟨ π₁ ∘ (⟨ f , g ⟩ ∘ h) , π₂ ∘ (⟨ f , g ⟩ ∘ h) ⟩
      ≡⟨ pair≡ (trans (sym (assoc _ _ _)) (∘l h (π₁-β f g)))
               (trans (sym (assoc _ _ _)) (∘l h (π₂-β f g))) ⟩
    ⟨ f ∘ h , g ∘ h ⟩ ∎

  pair-id : ∀ {A B} → ⟨ π₁ {A} {B} , π₂ ⟩ ≡ id
  pair-id = trans (pair≡ (sym (idr π₁)) (sym (idr π₂))) (⟨⟩-η id)

  pair-uni : ∀ {W A B} (h k : Hom W (A × B)) →
             π₁ ∘ h ≡ π₁ ∘ k → π₂ ∘ h ≡ π₂ ∘ k → h ≡ k
  pair-uni h k p q = trans (sym (⟨⟩-η h)) (trans (pair≡ p q) (⟨⟩-η k))

  !-∘ : ∀ {A B} (f : Hom A B) → ! ∘ f ≡ !
  !-∘ f = !-uni _

  𝟙-pt : (f : Hom 𝟙 𝟙) → f ≡ id
  𝟙-pt f = trans (!-uni f) (sym (!-uni id))

  []-∘ : ∀ {A B Y Z} (h : Hom Y Z) (f : Hom A Y) (g : Hom B Y) →
         h ∘ [ f , g ] ≡ [ h ∘ f , h ∘ g ]
  []-∘ h f g =
    trans (sym ([]-η _))
      (cong₂ [_,_] (trans (assoc _ _ _) (∘r h (ι₁-β f g)))
                   (trans (assoc _ _ _) (∘r h (ι₂-β f g))))

  copair-uni : ∀ {A B Y} (h k : Hom (A + B) Y) →
               h ∘ ι₁ ≡ k ∘ ι₁ → h ∘ ι₂ ≡ k ∘ ι₂ → h ≡ k
  copair-uni h k p q = trans (sym ([]-η h)) (trans (cong₂ [_,_] p q) ([]-η k))

  -- f ⊠ g
  _⊠_ : ∀ {A B C D} → Hom A C → Hom B D → Hom (A × B) (C × D)
  f ⊠ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  ⊠-∘pair : ∀ {W A B C D} (f : Hom A C) (g : Hom B D) (a : Hom W A) (b : Hom W B) →
            (f ⊠ g) ∘ ⟨ a , b ⟩ ≡ ⟨ f ∘ a , g ∘ b ⟩
  ⊠-∘pair f g a b =
    trans (⟨⟩-∘ _ _ _)
      (pair≡ (trans (assoc _ _ _) (∘r f (π₁-β a b)))
             (trans (assoc _ _ _) (∘r g (π₂-β a b))))

  ----------------------------------------------------------------------
  -- Exponentials: application and extensionality

  app : ∀ {W A B} → Hom W (Exp A B) → Hom W A → Hom W B
  app φ a = ev ∘ ⟨ φ , a ⟩

  app-∘ : ∀ {V W A B} (φ : Hom W (Exp A B)) (a : Hom W A) (h : Hom V W) →
          app φ a ∘ h ≡ app (φ ∘ h) (a ∘ h)
  app-∘ φ a h = trans (assoc _ _ _) (∘r ev (⟨⟩-∘ φ a h))

  app-lam : ∀ {V W A B} (f : Hom (W × A) B) (h : Hom V W) (a : Hom V A) →
            app (lam f ∘ h) a ≡ f ∘ ⟨ h , a ⟩
  app-lam f h a =
    ev ∘ ⟨ lam f ∘ h , a ⟩
      ≡⟨ ∘r ev (pair≡ (trans (∘r (lam f) (sym (π₁-β h a))) (sym (assoc _ _ _)))
                      (sym (π₂-β h a))) ⟩
    ev ∘ ⟨ (lam f ∘ π₁) ∘ ⟨ h , a ⟩ , π₂ ∘ ⟨ h , a ⟩ ⟩
      ≡⟨ ∘r ev (sym (⟨⟩-∘ _ _ _)) ⟩
    ev ∘ (⟨ lam f ∘ π₁ , π₂ ⟩ ∘ ⟨ h , a ⟩)
      ≡⟨ sym (assoc _ _ _) ⟩
    (ev ∘ ⟨ lam f ∘ π₁ , π₂ ⟩) ∘ ⟨ h , a ⟩
      ≡⟨ ∘l _ (lam-β f) ⟩
    f ∘ ⟨ h , a ⟩ ∎

  -- two maps into an exponential are equal if they agree pointwise
  ext : ∀ {W A B} (φ ψ : Hom W (Exp A B)) →
        app (φ ∘ π₁) π₂ ≡ app (ψ ∘ π₁) π₂ → φ ≡ ψ
  ext φ ψ p = trans (sym (lam-η φ)) (trans (cong lam p) (lam-η ψ))

  lam-nat : ∀ {V W A B} (f : Hom (W × A) B) (h : Hom V W) →
            lam f ∘ h ≡ lam (f ∘ (h ⊠ id))
  lam-nat f h =
    trans (sym (lam-η _))
      (cong lam
        (app ((lam f ∘ h) ∘ π₁) π₂
           ≡⟨ cong (λ x → app x π₂) (assoc _ _ _) ⟩
         app (lam f ∘ (h ∘ π₁)) π₂
           ≡⟨ app-lam f (h ∘ π₁) π₂ ⟩
         f ∘ ⟨ h ∘ π₁ , π₂ ⟩
           ≡⟨ ∘r f (pair≡ refl (sym (idl π₂))) ⟩
         f ∘ (h ⊠ id) ∎))

  ----------------------------------------------------------------------
  -- Case analysis on a coproduct factor of the input (distributivity)

  case : ∀ {B C X Y} (h k : Hom ((B + C) × X) Y) →
         h ∘ (ι₁ ⊠ id) ≡ k ∘ (ι₁ ⊠ id) → h ∘ (ι₂ ⊠ id) ≡ k ∘ (ι₂ ⊠ id) → h ≡ k
  case h k p q =
    h ≡⟨ sym (lam-β h) ⟩
    ev ∘ ⟨ lam h ∘ π₁ , π₂ ⟩
      ≡⟨ ∘r ev (pair≡ (∘l π₁ lh≡lk) refl) ⟩
    ev ∘ ⟨ lam k ∘ π₁ , π₂ ⟩
      ≡⟨ lam-β k ⟩
    k ∎
    where
      lh≡lk : lam h ≡ lam k
      lh≡lk = copair-uni (lam h) (lam k)
                (trans (lam-nat h ι₁) (trans (cong lam p) (sym (lam-nat k ι₁))))
                (trans (lam-nat h ι₂) (trans (cong lam q) (sym (lam-nat k ι₂))))

  cases : ∀ {B C X Y} → Hom (B × X) Y → Hom (C × X) Y → Hom ((B + C) × X) Y
  cases f g = ev ∘ ⟨ [ lam f , lam g ] ∘ π₁ , π₂ ⟩

  cases-β₁ : ∀ {B C X Y} (f : Hom (B × X) Y) (g : Hom (C × X) Y) →
             cases f g ∘ (ι₁ ⊠ id) ≡ f
  cases-β₁ f g =
    cases f g ∘ (ι₁ ⊠ id)
      ≡⟨ app-∘ _ _ _ ⟩
    app (([ lam f , lam g ] ∘ π₁) ∘ (ι₁ ⊠ id)) (π₂ ∘ (ι₁ ⊠ id))
      ≡⟨ cong₂ app
           (trans (assoc _ _ _)
             (trans (∘r _ (π₁-β _ _))
               (trans (sym (assoc _ _ _)) (∘l π₁ (ι₁-β _ _)))))
           (trans (π₂-β _ _) (idl π₂)) ⟩
    app (lam f ∘ π₁) π₂
      ≡⟨ app-lam f π₁ π₂ ⟩
    f ∘ ⟨ π₁ , π₂ ⟩
      ≡⟨ ∘r f (trans (pair≡ (sym (idr π₁)) (sym (idr π₂))) (⟨⟩-η id)) ⟩
    f ∘ id
      ≡⟨ idr f ⟩
    f ∎

  cases-β₂ : ∀ {B C X Y} (f : Hom (B × X) Y) (g : Hom (C × X) Y) →
             cases f g ∘ (ι₂ ⊠ id) ≡ g
  cases-β₂ f g =
    cases f g ∘ (ι₂ ⊠ id)
      ≡⟨ app-∘ _ _ _ ⟩
    app (([ lam f , lam g ] ∘ π₁) ∘ (ι₂ ⊠ id)) (π₂ ∘ (ι₂ ⊠ id))
      ≡⟨ cong₂ app
           (trans (assoc _ _ _)
             (trans (∘r _ (π₁-β _ _))
               (trans (sym (assoc _ _ _)) (∘l π₁ (ι₂-β _ _)))))
           (trans (π₂-β _ _) (idl π₂)) ⟩
    app (lam g ∘ π₁) π₂
      ≡⟨ app-lam g π₁ π₂ ⟩
    g ∘ ⟨ π₁ , π₂ ⟩
      ≡⟨ ∘r g (trans (pair≡ (sym (idr π₁)) (sym (idr π₂))) (⟨⟩-η id)) ⟩
    g ∘ id
      ≡⟨ idr g ⟩
    g ∎

  -- evaluating `cases` at an injected generalised element
  ⊠pair : ∀ {W B C X} (i : Hom B C) (b : Hom W B) (x : Hom W X) →
          ⟨ i ∘ b , x ⟩ ≡ (i ⊠ id) ∘ ⟨ b , x ⟩
  ⊠pair i b x = trans (pair≡ refl (sym (idl x))) (sym (⊠-∘pair i id b x))

  cases-at₁ : ∀ {W B C X Y} (f : Hom (B × X) Y) (g : Hom (C × X) Y)
              (b : Hom W B) (x : Hom W X) →
              cases f g ∘ ⟨ ι₁ ∘ b , x ⟩ ≡ f ∘ ⟨ b , x ⟩
  cases-at₁ f g b x =
    trans (∘r _ (⊠pair ι₁ b x))
      (trans (sym (assoc _ _ _)) (∘l _ (cases-β₁ f g)))

  cases-at₂ : ∀ {W B C X Y} (f : Hom (B × X) Y) (g : Hom (C × X) Y)
              (c : Hom W C) (x : Hom W X) →
              cases f g ∘ ⟨ ι₂ ∘ c , x ⟩ ≡ g ∘ ⟨ c , x ⟩
  cases-at₂ f g c x =
    trans (∘r _ (⊠pair ι₂ c x))
      (trans (sym (assoc _ _ _)) (∘l _ (cases-β₂ f g)))

  ----------------------------------------------------------------------
  -- Booleans

  𝟚 : Ob
  𝟚 = 𝟙 + 𝟙

  ff tt : ∀ {W} → Hom W 𝟚
  ff = ι₁ ∘ !
  tt = ι₂ ∘ !

  ff-∘ : ∀ {V W} (h : Hom V W) → ff ∘ h ≡ ff
  ff-∘ h = trans (assoc _ _ _) (∘r ι₁ (!-∘ h))

  tt-∘ : ∀ {V W} (h : Hom V W) → tt ∘ h ≡ tt
  tt-∘ h = trans (assoc _ _ _) (∘r ι₂ (!-∘ h))

  -- and(ff, y) = ff, and(tt, y) = y
  and : Hom (𝟚 × 𝟚) 𝟚
  and = cases ff π₂

  infixr 7 _∧_
  _∧_ : ∀ {W} → Hom W 𝟚 → Hom W 𝟚 → Hom W 𝟚
  a ∧ b = and ∘ ⟨ a , b ⟩

  ∧-∘ : ∀ {V W} (a b : Hom W 𝟚) (h : Hom V W) → (a ∧ b) ∘ h ≡ (a ∘ h) ∧ (b ∘ h)
  ∧-∘ a b h = trans (assoc _ _ _) (∘r and (⟨⟩-∘ a b h))

  ∧-cong : ∀ {W} {a a′ b b′ : Hom W 𝟚} → a ≡ a′ → b ≡ b′ → a ∧ b ≡ a′ ∧ b′
  ∧-cong refl refl = refl

  ff-∧ : ∀ {W} (b : Hom W 𝟚) → ff ∧ b ≡ ff
  ff-∧ b =
    trans (cases-at₁ ff π₂ ! b) (ff-∘ _)

  tt-∧ : ∀ {W} (b : Hom W 𝟚) → tt ∧ b ≡ b
  tt-∧ b = trans (cases-at₂ ff π₂ ! b) (π₂-β ! b)

  -- associativity, by cases on the first argument
  ∧-assoc : ∀ {W} (a b c : Hom W 𝟚) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc {W} a b c =
    (a ∧ b) ∧ c
      ≡⟨ gen-at ⟩
    L ∘ ⟨ a , ⟨ b , c ⟩ ⟩
      ≡⟨ ∘l _ L≡R ⟩
    R ∘ ⟨ a , ⟨ b , c ⟩ ⟩
      ≡⟨ gen-at′ ⟩
    a ∧ (b ∧ c) ∎
    where
      X = 𝟚 × 𝟚
      p₁ : Hom (𝟚 × X) 𝟚
      p₁ = π₁
      y z : Hom (𝟚 × X) 𝟚
      y = π₁ ∘ π₂
      z = π₂ ∘ π₂
      L R : Hom (𝟚 × X) 𝟚
      L = (p₁ ∧ y) ∧ z
      R = p₁ ∧ (y ∧ z)
      sel : Hom (W × X) X
      sel = π₂
      -- on ff
      Lff : L ∘ (ι₁ ⊠ id) ≡ R ∘ (ι₁ ⊠ id)
      Lff =
        L ∘ (ι₁ ⊠ id)
          ≡⟨ ∧-∘ _ _ _ ⟩
        ((p₁ ∧ y) ∘ (ι₁ ⊠ id)) ∧ (z ∘ (ι₁ ⊠ id))
          ≡⟨ ∧-cong (∧-∘ _ _ _) refl ⟩
        ((p₁ ∘ (ι₁ ⊠ id)) ∧ (y ∘ (ι₁ ⊠ id))) ∧ (z ∘ (ι₁ ⊠ id))
          ≡⟨ ∧-cong (∧-cong p₁ι₁ refl) refl ⟩
        (ff ∧ (y ∘ (ι₁ ⊠ id))) ∧ (z ∘ (ι₁ ⊠ id))
          ≡⟨ ∧-cong (ff-∧ _) refl ⟩
        ff ∧ (z ∘ (ι₁ ⊠ id))
          ≡⟨ ff-∧ _ ⟩
        ff
          ≡⟨ sym (ff-∧ _) ⟩
        ff ∧ ((y ∧ z) ∘ (ι₁ ⊠ id))
          ≡⟨ ∧-cong (sym p₁ι₁) refl ⟩
        (p₁ ∘ (ι₁ ⊠ id)) ∧ ((y ∧ z) ∘ (ι₁ ⊠ id))
          ≡⟨ sym (∧-∘ _ _ _) ⟩
        R ∘ (ι₁ ⊠ id) ∎
        where
          p₁ι₁ : p₁ ∘ (ι₁ ⊠ id) ≡ ff
          p₁ι₁ = trans (π₁-β _ _) (∘r ι₁ (!-uni π₁))
      Ltt : L ∘ (ι₂ ⊠ id) ≡ R ∘ (ι₂ ⊠ id)
      Ltt =
        L ∘ (ι₂ ⊠ id)
          ≡⟨ ∧-∘ _ _ _ ⟩
        ((p₁ ∧ y) ∘ (ι₂ ⊠ id)) ∧ (z ∘ (ι₂ ⊠ id))
          ≡⟨ ∧-cong (∧-∘ _ _ _) refl ⟩
        ((p₁ ∘ (ι₂ ⊠ id)) ∧ (y ∘ (ι₂ ⊠ id))) ∧ (z ∘ (ι₂ ⊠ id))
          ≡⟨ ∧-cong (∧-cong p₁ι₂ refl) refl ⟩
        (tt ∧ (y ∘ (ι₂ ⊠ id))) ∧ (z ∘ (ι₂ ⊠ id))
          ≡⟨ ∧-cong (tt-∧ _) refl ⟩
        (y ∘ (ι₂ ⊠ id)) ∧ (z ∘ (ι₂ ⊠ id))
          ≡⟨ sym (∧-∘ _ _ _) ⟩
        (y ∧ z) ∘ (ι₂ ⊠ id)
          ≡⟨ sym (tt-∧ _) ⟩
        tt ∧ ((y ∧ z) ∘ (ι₂ ⊠ id))
          ≡⟨ ∧-cong (sym p₁ι₂) refl ⟩
        (p₁ ∘ (ι₂ ⊠ id)) ∧ ((y ∧ z) ∘ (ι₂ ⊠ id))
          ≡⟨ sym (∧-∘ _ _ _) ⟩
        R ∘ (ι₂ ⊠ id) ∎
        where
          p₁ι₂ : p₁ ∘ (ι₂ ⊠ id) ≡ tt
          p₁ι₂ = trans (π₁-β _ _) (∘r ι₂ (!-uni π₁))
      L≡R : L ≡ R
      L≡R = case L R Lff Ltt
      t = ⟨ a , ⟨ b , c ⟩ ⟩
      yt : y ∘ t ≡ b
      yt = trans (assoc _ _ _) (trans (∘r π₁ (π₂-β _ _)) (π₁-β _ _))
      zt : z ∘ t ≡ c
      zt = trans (assoc _ _ _) (trans (∘r π₂ (π₂-β _ _)) (π₂-β _ _))
      gen-at : (a ∧ b) ∧ c ≡ L ∘ t
      gen-at = sym (trans (∧-∘ _ _ _)
                     (∧-cong (trans (∧-∘ _ _ _) (∧-cong (π₁-β _ _) yt)) zt))
      gen-at′ : R ∘ t ≡ a ∧ (b ∧ c)
      gen-at′ = trans (∧-∘ _ _ _)
                  (∧-cong (π₁-β _ _) (trans (∧-∘ _ _ _) (∧-cong yt zt)))

  ----------------------------------------------------------------------
  -- Pointwise ∧ on an exponential, sequences, shift

  andE : ∀ {A} → Hom (Exp A 𝟚 × Exp A 𝟚) (Exp A 𝟚)
  andE = lam (app (π₁ ∘ π₁) π₂ ∧ app (π₂ ∘ π₁) π₂)

  app-andE : ∀ {W A} (φ ψ : Hom W (Exp A 𝟚)) (a : Hom W A) →
             app (andE ∘ ⟨ φ , ψ ⟩) a ≡ app φ a ∧ app ψ a
  app-andE φ ψ a =
    app (andE ∘ ⟨ φ , ψ ⟩) a
      ≡⟨ app-lam _ _ _ ⟩
    (app (π₁ ∘ π₁) π₂ ∧ app (π₂ ∘ π₁) π₂) ∘ ⟨ ⟨ φ , ψ ⟩ , a ⟩
      ≡⟨ ∧-∘ _ _ _ ⟩
    (app (π₁ ∘ π₁) π₂ ∘ ⟨ ⟨ φ , ψ ⟩ , a ⟩) ∧ (app (π₂ ∘ π₁) π₂ ∘ ⟨ ⟨ φ , ψ ⟩ , a ⟩)
      ≡⟨ ∧-cong (trans (app-∘ _ _ _) (cong₂ app (sel₁ π₁ φ (π₁-β _ _)) (π₂-β _ _)))
                (trans (app-∘ _ _ _) (cong₂ app (sel₁ π₂ ψ (π₂-β _ _)) (π₂-β _ _))) ⟩
    app φ a ∧ app ψ a ∎
    where
      sel₁ : ∀ {Q} (pr : Hom (Exp _ 𝟚 × Exp _ 𝟚) Q) (r : Hom _ Q) →
             pr ∘ ⟨ φ , ψ ⟩ ≡ r → (pr ∘ π₁) ∘ ⟨ ⟨ φ , ψ ⟩ , a ⟩ ≡ r
      sel₁ pr r e = trans (assoc _ _ _) (trans (∘r pr (π₁-β _ _)) e)

  S : Ob
  S = Exp N 𝟚

  shift : Hom S S
  shift = lam (app π₁ (suc ∘ π₂))

  app-shift : ∀ {W} (u : Hom W S) (n : Hom W N) →
              app (shift ∘ u) n ≡ app u (suc ∘ n)
  app-shift u n =
    trans (app-lam _ _ _)
      (trans (app-∘ _ _ _)
        (cong₂ app (π₁-β _ _) (trans (assoc _ _ _) (∘r suc (π₂-β _ _)))))

  -- decreasing sequences:  u(n+1) = u(n) ∧ u(n+1)
  M : Ob
  M = Eq shift (andE ∘ ⟨ id , shift ⟩)

  m : Hom M S
  m = eqm

  -- the defining equation, pointwise
  dec : ∀ {W} (u : Hom W M) (n : Hom W N) →
        app (m ∘ u) (suc ∘ n) ≡ app (m ∘ u) n ∧ app (m ∘ u) (suc ∘ n)
  dec u n =
    app (m ∘ u) (suc ∘ n)
      ≡⟨ sym (app-shift _ _) ⟩
    app (shift ∘ (m ∘ u)) n
      ≡⟨ cong (λ x → app x n) (trans (sym (assoc _ _ _)) (trans (∘l u eqm-eq) (assoc _ _ _))) ⟩
    app ((andE ∘ ⟨ id , shift ⟩) ∘ (m ∘ u)) n
      ≡⟨ cong (λ x → app x n) (trans (assoc _ _ _) (∘r andE (⟨⟩-∘ _ _ _))) ⟩
    app (andE ∘ ⟨ id ∘ (m ∘ u) , shift ∘ (m ∘ u) ⟩) n
      ≡⟨ app-andE _ _ _ ⟩
    app (id ∘ (m ∘ u)) n ∧ app (shift ∘ (m ∘ u)) n
      ≡⟨ ∧-cong (cong (λ x → app x n) (idl _)) (app-shift _ _) ⟩
    app (m ∘ u) n ∧ app (m ∘ u) (suc ∘ n) ∎

  -- membership in M from the pointwise condition
  intoM : ∀ {W} (v : Hom W S) →
          (∀ {V} (h : Hom V W) (n : Hom V N) →
             app (v ∘ h) (suc ∘ n) ≡ app (v ∘ h) n ∧ app (v ∘ h) (suc ∘ n)) →
          shift ∘ v ≡ (andE ∘ ⟨ id , shift ⟩) ∘ v
  intoM v p =
    ext _ _
      (app ((shift ∘ v) ∘ π₁) π₂
         ≡⟨ cong (λ x → app x π₂) (assoc _ _ _) ⟩
       app (shift ∘ (v ∘ π₁)) π₂
         ≡⟨ app-shift _ _ ⟩
       app (v ∘ π₁) (suc ∘ π₂)
         ≡⟨ p π₁ π₂ ⟩
       app (v ∘ π₁) π₂ ∧ app (v ∘ π₁) (suc ∘ π₂)
         ≡⟨ ∧-cong (cong (λ x → app x π₂) (sym (idl _))) (sym (app-shift _ _)) ⟩
       app (id ∘ (v ∘ π₁)) π₂ ∧ app (shift ∘ (v ∘ π₁)) π₂
         ≡⟨ sym (app-andE _ _ _) ⟩
       app (andE ∘ ⟨ id ∘ (v ∘ π₁) , shift ∘ (v ∘ π₁) ⟩) π₂
         ≡⟨ cong (λ x → app x π₂)
              (trans (∘r andE (sym (⟨⟩-∘ _ _ _)))
                (trans (sym (assoc _ _ _)) (sym (assoc _ _ _)))) ⟩
       app (((andE ∘ ⟨ id , shift ⟩) ∘ v) ∘ π₁) π₂ ∎)

  ----------------------------------------------------------------------
  -- Structure of M: head, pred, zero, out

  head : Hom M 𝟚
  head = app m (zero ∘ !)

  pred : Hom M M
  pred = fact (shift ∘ m)
           (intoM (shift ∘ m) λ h n →
              trans (cong (λ x → app x (suc ∘ n)) (assoc _ _ _))
                (trans (app-shift _ _)
                  (trans (dec h (suc ∘ n))
                    (sym (∧-cong (trans (cong (λ x → app x n) (assoc _ _ _)) (app-shift _ _))
                                 (trans (cong (λ x → app x (suc ∘ n)) (assoc _ _ _))
                                        (app-shift _ _)))))))

  m-pred : m ∘ pred ≡ shift ∘ m
  m-pred = fact-β _ _

  zeroS : ∀ {W} → Hom W S
  zeroS = lam ff

  app-zeroS : ∀ {W} (n : Hom W N) → app (zeroS {W}) n ≡ ff
  app-zeroS n =
    trans (cong (λ x → app x n) (sym (idr _)))
      (trans (app-lam _ _ _) (ff-∘ _))

  app-zeroS′ : ∀ {V W} {h : Hom V W} (k : Hom V N) →
               app (lam (ff ∘ (h ⊠ id))) k ≡ ff
  app-zeroS′ {h = h} k =
    trans (cong (λ x → app x k) (sym (idr _)))
      (trans (app-lam _ _ _) (trans (assoc _ _ _) (ff-∘ _)))

  app-zeroS-∘ : ∀ {V W} (h : Hom V W) (n : Hom V N) → app (zeroS {W} ∘ h) n ≡ ff
  app-zeroS-∘ h n = trans (cong (λ x → app x n) (lam-nat _ h)) (app-zeroS′ n)

  zeroM : ∀ {W} → Hom W M
  zeroM = fact zeroS
            (intoM zeroS λ h n →
               trans (app-zeroS-∘ h _)
                 (sym (trans (∧-cong (app-zeroS-∘ h _) (app-zeroS-∘ h _)) (ff-∧ _))))

  m-zeroM : ∀ {W} → m ∘ zeroM {W} ≡ zeroS
  m-zeroM = fact-β _ _

  out : Hom M (𝟙 + M)
  out = cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ ⟨ head , pred ⟩

  app≡′ : ∀ {W A B} {φ ψ : Hom W (Exp A B)} (a : Hom W A) → φ ≡ ψ → app φ a ≡ app ψ a
  app≡′ a refl = refl

  -- induction: the equaliser of f, g : N → Y is closed under zero and suc
  ind : ∀ {Y} (f g : Hom N Y) → f ∘ zero ≡ g ∘ zero →
        (∀ {W} (k : Hom W N) → f ∘ k ≡ g ∘ k → f ∘ (suc ∘ k) ≡ g ∘ (suc ∘ k)) →
        f ≡ g
  ind {Y} f g base step′ =
    f ≡⟨ sym (idr f) ⟩
    f ∘ id ≡⟨ ∘r f (sym ej) ⟩
    f ∘ (e ∘ j) ≡⟨ sym (assoc _ _ _) ⟩
    (f ∘ e) ∘ j ≡⟨ ∘l j eqm-eq ⟩
    (g ∘ e) ∘ j ≡⟨ assoc _ _ _ ⟩
    g ∘ (e ∘ j) ≡⟨ ∘r g ej ⟩
    g ∘ id ≡⟨ idr g ⟩
    g ∎
    where
      e : Hom (Eq f g) N
      e = eqm
      zE : Hom 𝟙 (Eq f g)
      zE = fact zero base
      sE : Hom (Eq f g) (Eq f g)
      sE = fact (suc ∘ e) (step′ e eqm-eq)
      j : Hom N (Eq f g)
      j = it zE sE
      ej : e ∘ j ≡ id
      ej = trans (it-uni zero suc (e ∘ j)
                    (trans (assoc _ _ _) (trans (∘r e (it-z zE sE)) (fact-β _ _)))
                    (trans (assoc _ _ _)
                      (trans (∘r e (it-s zE sE))
                        (trans (sym (assoc _ _ _))
                          (trans (∘l j (fact-β _ _)) (assoc _ _ _))))))
                 (sym (it-uni zero suc id (idl zero) (trans (idl suc) (sym (idr suc)))))

  -- on M, u(0) ∧ u(n+1) = u(n+1)
  private
    fD gD : Hom N (Exp M 𝟚)
    fD = lam (app (m ∘ π₂) (suc ∘ π₁))
    gD = lam (app (m ∘ π₂) (zero ∘ !) ∧ app (m ∘ π₂) (suc ∘ π₁))

    pick : ∀ {W} (k : Hom W N) (u : Hom W M) → (m ∘ π₂) ∘ ⟨ k , u ⟩ ≡ m ∘ u
    pick k u = trans (assoc _ _ _) (∘r m (π₂-β _ _))

    app-fD : ∀ {W} (k : Hom W N) (u : Hom W M) → app (fD ∘ k) u ≡ app (m ∘ u) (suc ∘ k)
    app-fD k u =
      trans (app-lam _ _ _)
        (trans (app-∘ _ _ _)
          (cong₂ app (pick k u) (trans (assoc _ _ _) (∘r suc (π₁-β _ _)))))

    app-gD : ∀ {W} (k : Hom W N) (u : Hom W M) →
             app (gD ∘ k) u ≡ app (m ∘ u) (zero ∘ !) ∧ app (m ∘ u) (suc ∘ k)
    app-gD k u =
      trans (app-lam _ _ _)
        (trans (∧-∘ _ _ _)
          (∧-cong (trans (app-∘ _ _ _)
                     (cong₂ app (pick k u) (trans (assoc _ _ _) (∘r zero (!-∘ _)))))
                  (trans (app-∘ _ _ _)
                     (cong₂ app (pick k u) (trans (assoc _ _ _) (∘r suc (π₁-β _ _)))))))

    ptw : ∀ {W} {φ ψ : Hom W (Exp M 𝟚)} → φ ≡ ψ →
          app (φ ∘ π₁) π₂ ≡ app (ψ ∘ π₁) π₂
    ptw refl = refl

    fD≡gD : fD ≡ gD
    fD≡gD = ind fD gD base stp
      where
        base : fD ∘ zero ≡ gD ∘ zero
        base = ext _ _
          (app ((fD ∘ zero) ∘ π₁) π₂
             ≡⟨ trans (app≡′ π₂ (assoc _ _ _)) (app-fD _ _) ⟩
           app (m ∘ π₂) (suc ∘ (zero ∘ π₁))
             ≡⟨ dec π₂ (zero ∘ π₁) ⟩
           app (m ∘ π₂) (zero ∘ π₁) ∧ app (m ∘ π₂) (suc ∘ (zero ∘ π₁))
             ≡⟨ ∧-cong (cong (app (m ∘ π₂)) (∘r zero (!-uni π₁))) refl ⟩
           app (m ∘ π₂) (zero ∘ !) ∧ app (m ∘ π₂) (suc ∘ (zero ∘ π₁))
             ≡⟨ sym (trans (app≡′ π₂ (assoc _ _ _)) (app-gD _ _)) ⟩
           app ((gD ∘ zero) ∘ π₁) π₂ ∎)
        stp : ∀ {W} (k : Hom W N) → fD ∘ k ≡ gD ∘ k → fD ∘ (suc ∘ k) ≡ gD ∘ (suc ∘ k)
        stp k hyp = ext _ _
          (app ((fD ∘ (suc ∘ k)) ∘ π₁) π₂
             ≡⟨ trans (app≡′ π₂ (assoc _ _ _)) (trans (app-fD _ _) s2) ⟩
           a2
             ≡⟨ dec π₂ (suc ∘ (k ∘ π₁)) ⟩
           a1 ∧ a2
             ≡⟨ ∧-cong h1 refl ⟩
           (z0 ∧ a1) ∧ a2
             ≡⟨ ∧-assoc _ _ _ ⟩
           z0 ∧ (a1 ∧ a2)
             ≡⟨ ∧-cong refl (sym (dec π₂ (suc ∘ (k ∘ π₁)))) ⟩
           z0 ∧ a2
             ≡⟨ sym (trans (app≡′ π₂ (assoc _ _ _)) (trans (app-gD _ _) (∧-cong refl s2))) ⟩
           app ((gD ∘ (suc ∘ k)) ∘ π₁) π₂ ∎)
          where
            u = π₂
            z0 = app (m ∘ u) (zero ∘ !)
            a1 = app (m ∘ u) (suc ∘ (k ∘ π₁))
            a2 = app (m ∘ u) (suc ∘ (suc ∘ (k ∘ π₁)))
            s2 : app (m ∘ u) (suc ∘ ((suc ∘ k) ∘ π₁)) ≡ a2
            s2 = cong (app (m ∘ u)) (∘r suc (assoc _ _ _))
            h1 : a1 ≡ z0 ∧ a1
            h1 = trans (sym (app-fD _ _))
                   (trans (app≡′ π₂ (sym (assoc _ _ _)))
                     (trans (ptw hyp)
                       (trans (app≡′ π₂ (assoc _ _ _)) (app-gD _ _))))

  decAll : ∀ {W} (u : Hom W M) (n : Hom W N) →
           app (m ∘ u) (zero ∘ !) ∧ app (m ∘ u) (suc ∘ n) ≡ app (m ∘ u) (suc ∘ n)
  decAll u n = trans (sym (app-gD n u)) (trans (app≡′ u (∘l n (sym fD≡gD))) (app-fD n u))

  zeroS-∘ : ∀ {V W} (h : Hom V W) → zeroS {W} ∘ h ≡ zeroS {V}
  zeroS-∘ h = trans (lam-nat _ h) (cong lam (ff-∘ _))

  -- the two projections out of 1 + M
  σ : Hom (𝟙 + M) 𝟚
  σ = [ ι₁ , ι₂ ∘ ! ]

  τ : Hom (𝟙 + M) M
  τ = [ zeroM , id ]

  σ-out : σ ∘ out ≡ head
  σ-out =
    trans (sym (assoc _ _ _)) (trans (∘l _ gen) (π₁-β _ _))
    where
      gen : σ ∘ cases (ι₁ ∘ !) (ι₂ ∘ π₂) ≡ π₁
      gen = case _ _
        (trans (assoc _ _ _)
          (trans (∘r σ (cases-β₁ _ _))
            (trans (sym (assoc _ _ _))
              (trans (∘l ! (ι₁-β _ _))
                (sym (trans (π₁-β _ _) (∘r ι₁ (!-uni π₁))))))))
        (trans (assoc _ _ _)
          (trans (∘r σ (cases-β₂ _ _))
            (trans (sym (assoc _ _ _))
              (trans (∘l π₂ (ι₂-β _ _))
                (trans (assoc _ _ _)
                  (trans (∘r ι₂ (!-uni _))
                    (sym (trans (π₁-β _ _) (∘r ι₂ (!-uni π₁))))))))))

  τ-out : τ ∘ out ≡ pred
  τ-out =
    eqm-mono _ _
      (trans (sym (assoc _ _ _))
        (trans (∘l out mτ)
          (trans (sym (assoc _ _ _))
            (trans (∘l _ gen)
              (trans (ext _ _ pt) (sym m-pred))))))
    where
      mτ : m ∘ τ ≡ [ zeroS , m ]
      mτ = trans ([]-∘ m zeroM id) (cong₂ [_,_] m-zeroM (idr m))
      gen : [ zeroS , m ] ∘ cases (ι₁ ∘ !) (ι₂ ∘ π₂) ≡ cases zeroS (m ∘ π₂)
      gen = case _ _
        (trans (assoc _ _ _)
          (trans (∘r _ (cases-β₁ _ _))
            (trans (sym (assoc _ _ _))
              (trans (∘l ! (ι₁-β _ _)) (trans (zeroS-∘ !) (sym (cases-β₁ _ _)))))))
        (trans (assoc _ _ _)
          (trans (∘r _ (cases-β₂ _ _))
            (trans (sym (assoc _ _ _))
              (trans (∘l π₂ (ι₂-β _ _)) (sym (cases-β₂ _ _))))))
      -- generic: app (cases zeroS (m ∘ π₂) ∘ ⟨ b , p ⟩) n = b ∧ app (m ∘ p) n
      Q = 𝟚 × (M × N)
      L R : Hom Q 𝟚
      L = app (cases zeroS (m ∘ π₂) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩) (π₂ ∘ π₂)
      R = π₁ ∧ app (m ∘ (π₁ ∘ π₂)) (π₂ ∘ π₂)
      inj : ∀ {B} (i : Hom B 𝟚) → ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ (i ⊠ id {M × N}) ≡ ⟨ i ∘ π₁ , π₁ ∘ π₂ ⟩
      inj i = trans (⟨⟩-∘ _ _ _)
                (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (∘r π₁ (trans (π₂-β _ _) (idl π₂)))))
      sn : ∀ {B} (i : Hom B 𝟚) → (π₂ ∘ π₂) ∘ (i ⊠ id {M × N}) ≡ π₂ ∘ π₂
      sn i = trans (assoc _ _ _) (∘r π₂ (trans (π₂-β _ _) (idl π₂)))
      sm : ∀ {B} (i : Hom B 𝟚) → (m ∘ (π₁ ∘ π₂)) ∘ (i ⊠ id {M × N}) ≡ m ∘ (π₁ ∘ π₂)
      sm i = trans (assoc _ _ _) (∘r m (trans (assoc _ _ _) (∘r π₁ (trans (π₂-β _ _) (idl π₂)))))
      L≡R : L ≡ R
      L≡R = case L R
        (trans (app-∘ _ _ _)
          (trans (cong₂ app (trans (assoc _ _ _) (trans (∘r _ (inj ι₁))
                    (trans (∘r _ (pair≡ (∘r ι₁ (!-uni π₁)) refl)) (cases-at₁ _ _ _ _)))) (sn ι₁))
            (trans (app-zeroS-∘ _ _)
              (sym (trans (∧-∘ _ _ _)
                     (trans (∧-cong (trans (π₁-β _ _) (∘r ι₁ (!-uni π₁))) refl) (ff-∧ _)))))))
        (trans (app-∘ _ _ _)
          (trans (cong₂ app (trans (assoc _ _ _) (trans (∘r _ (inj ι₂))
                    (trans (∘r _ (pair≡ (∘r ι₂ (!-uni π₁)) refl))
                      (trans (cases-at₂ _ _ _ _) (trans (assoc _ _ _) (∘r m (π₂-β _ _)))))))
                    (sn ι₂))
            (sym (trans (∧-∘ _ _ _)
                   (trans (∧-cong (trans (π₁-β _ _) (∘r ι₂ (!-uni π₁)))
                                  (trans (app-∘ _ _ _) (cong₂ app (sm ι₂) (sn ι₂))))
                     (tt-∧ _))))))
      at : ∀ {W} (b : Hom W 𝟚) (p : Hom W M) (n : Hom W N) →
           app (cases zeroS (m ∘ π₂) ∘ ⟨ b , p ⟩) n ≡ b ∧ app (m ∘ p) n
      at b p n =
        trans (sym (trans (app-∘ _ _ _)
                     (cong₂ app (trans (assoc _ _ _)
                                  (∘r _ (trans (⟨⟩-∘ _ _ _)
                                    (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (trans (∘r π₁ (π₂-β _ _)) (π₁-β _ _)))))))
                                (trans (assoc _ _ _) (trans (∘r π₂ (π₂-β _ _)) (π₂-β _ _))))))
          (trans (∘l _ L≡R)
            (trans (∧-∘ _ _ _)
              (∧-cong (π₁-β _ _)
                (trans (app-∘ _ _ _)
                  (cong₂ app (trans (assoc _ _ _) (∘r m (trans (assoc _ _ _) (trans (∘r π₁ (π₂-β _ _)) (π₁-β _ _)))))
                             (trans (assoc _ _ _) (trans (∘r π₂ (π₂-β _ _)) (π₂-β _ _))))))))
      pt : app (((cases zeroS (m ∘ π₂)) ∘ ⟨ head , pred ⟩) ∘ π₁) π₂ ≡ app ((shift ∘ m) ∘ π₁) π₂
      pt =
        app ((cases zeroS (m ∘ π₂) ∘ ⟨ head , pred ⟩) ∘ π₁) π₂
          ≡⟨ app≡′ π₂ (trans (assoc _ _ _) (∘r _ (⟨⟩-∘ _ _ _))) ⟩
        app (cases zeroS (m ∘ π₂) ∘ ⟨ head ∘ π₁ , pred ∘ π₁ ⟩) π₂
          ≡⟨ at _ _ _ ⟩
        (head ∘ π₁) ∧ app (m ∘ (pred ∘ π₁)) π₂
          ≡⟨ ∧-cong (trans (app-∘ _ _ _) (cong (app (m ∘ π₁)) (trans (assoc _ _ _) (∘r zero (!-∘ _)))))
                    (trans (app≡′ π₂ (trans (sym (assoc _ _ _)) (trans (∘l π₁ m-pred) (assoc _ _ _))))
                           (app-shift _ _)) ⟩
        app (m ∘ π₁) (zero ∘ !) ∧ app (m ∘ π₁) (suc ∘ π₂)
          ≡⟨ decAll π₁ π₂ ⟩
        app (m ∘ π₁) (suc ∘ π₂)
          ≡⟨ sym (trans (app≡′ π₂ (trans (assoc _ _ _) (sym (assoc _ _ _)))) (trans (app≡′ π₂ (assoc _ _ _)) (app-shift _ _))) ⟩
        app ((shift ∘ m) ∘ π₁) π₂ ∎

  ----------------------------------------------------------------------
  -- Coalgebras of 1 + X

  module Final {C : Ob} (c : Hom C (𝟙 + C)) where

    IsMor : Hom C M → Set
    IsMor g = out ∘ g ≡ [ ι₁ , ι₂ ∘ g ] ∘ c

    χ : Hom C 𝟚
    χ = [ ι₁ , ι₂ ∘ ! ] ∘ c

    E : Ob
    E = Exp C 𝟚

    -- step φ = λx. [ff, φ](c x)
    K : Hom ((𝟙 + C) × E) 𝟚
    K = cases ff (ev ∘ ⟨ π₂ , π₁ ⟩)

    step : Hom E E
    step = lam (K ∘ ⟨ c ∘ π₂ , π₁ ⟩)

    app-step : ∀ {W} (φ : Hom W E) (x : Hom W C) →
               app (step ∘ φ) x ≡ K ∘ ⟨ c ∘ x , φ ⟩
    app-step φ x =
      trans (app-lam _ _ _)
        (trans (assoc _ _ _)
          (∘r K (trans (⟨⟩-∘ _ _ _)
                   (pair≡ (trans (assoc _ _ _) (∘r c (π₂-β _ _))) (π₁-β _ _)))))

    χ̂ : Hom 𝟙 E
    χ̂ = lam (χ ∘ π₂)

    r : Hom N E
    r = it χ̂ step

    -- K at an injected first argument
    K-ff : ∀ {W} (φ : Hom W E) → K ∘ ⟨ ι₁ ∘ ! , φ ⟩ ≡ ff
    K-ff φ = trans (cases-at₁ _ _ _ _) (ff-∘ _)

    K-in : ∀ {W} (y : Hom W C) (φ : Hom W E) → K ∘ ⟨ ι₂ ∘ y , φ ⟩ ≡ app φ y
    K-in y φ =
      trans (cases-at₂ _ _ _ _)
        (trans (assoc _ _ _) (∘r ev (trans (⟨⟩-∘ _ _ _) (pair≡ (π₂-β _ _) (π₁-β _ _)))))

    -- step preserves pointwise ∧
    step-∧ : ∀ {W} (φ ψ : Hom W E) (x : Hom W C) →
             K ∘ ⟨ c ∘ x , φ ⟩ ∧ K ∘ ⟨ c ∘ x , ψ ⟩ ≡ K ∘ ⟨ c ∘ x , andE ∘ ⟨ φ , ψ ⟩ ⟩
    step-∧ {W} φ ψ x =
      trans (sym gen) (trans (∘l _ G≡H) gen′)
      where
        Q = (𝟙 + C) × (E × E)
        G H : Hom Q 𝟚
        G = K ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∧ K ∘ ⟨ π₁ , π₂ ∘ π₂ ⟩
        H = K ∘ ⟨ π₁ , andE ∘ π₂ ⟩
        t : Hom W Q
        t = ⟨ c ∘ x , ⟨ φ , ψ ⟩ ⟩
        sel : ∀ {Z} (q : Hom (E × E) Z) (z : Hom W Z) → q ∘ ⟨ φ , ψ ⟩ ≡ z →
              ⟨ π₁ , q ∘ π₂ ⟩ ∘ t ≡ ⟨ c ∘ x , z ⟩
        sel q z e = trans (⟨⟩-∘ _ _ _)
                      (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (trans (∘r q (π₂-β _ _)) e)))
        gen : G ∘ t ≡ K ∘ ⟨ c ∘ x , φ ⟩ ∧ K ∘ ⟨ c ∘ x , ψ ⟩
        gen = trans (∧-∘ _ _ _)
                (∧-cong (trans (assoc _ _ _) (∘r K (sel π₁ φ (π₁-β _ _))))
                        (trans (assoc _ _ _) (∘r K (sel π₂ ψ (π₂-β _ _)))))
        gen′ : H ∘ t ≡ K ∘ ⟨ c ∘ x , andE ∘ ⟨ φ , ψ ⟩ ⟩
        gen′ = trans (assoc _ _ _) (∘r K (sel andE _ refl))
        at : ∀ {B} (i : Hom B (𝟙 + C)) (q : Hom (E × E) E) →
             ⟨ π₁ , q ∘ π₂ ⟩ ∘ (i ⊠ id) ≡ ⟨ i ∘ π₁ , q ∘ π₂ ⟩
        at i q = trans (⟨⟩-∘ _ _ _)
                   (pair≡ (π₁-β _ _)
                     (trans (assoc _ _ _) (∘r q (trans (π₂-β _ _) (idl π₂)))))
        Gff : G ∘ (ι₁ ⊠ id) ≡ H ∘ (ι₁ ⊠ id)
        Gff =
          trans (∧-∘ _ _ _)
            (trans (∧-cong (trans (assoc _ _ _) (trans (∘r K (at ι₁ π₁)) (ff′ _)))
                           (trans (assoc _ _ _) (trans (∘r K (at ι₁ π₂)) (ff′ _))))
              (trans (ff-∧ _)
                (sym (trans (assoc _ _ _) (trans (∘r K (at ι₁ andE)) (ff′ _))))))
          where
            ff′ : ∀ (q : Hom (𝟙 × (E × E)) E) → K ∘ ⟨ ι₁ ∘ π₁ , q ⟩ ≡ ff
            ff′ q = trans (∘r K (pair≡ (∘r ι₁ (!-uni π₁)) refl)) (K-ff q)
        Gtt : G ∘ (ι₂ ⊠ id) ≡ H ∘ (ι₂ ⊠ id)
        Gtt =
          trans (∧-∘ _ _ _)
            (trans (∧-cong (trans (assoc _ _ _) (trans (∘r K (at ι₂ π₁)) (K-in _ _)))
                           (trans (assoc _ _ _) (trans (∘r K (at ι₂ π₂)) (K-in _ _))))
              (trans (sym (app-andE _ _ _))
                (trans (cong (λ q → app q π₁) (∘r andE (trans (sym (⟨⟩-∘ π₁ π₂ π₂)) (trans (∘l π₂ pair-id) (idl π₂)))))
                  (sym (trans (assoc _ _ _) (trans (∘r K (at ι₂ andE)) (K-in _ _)))))))
        G≡H : G ≡ H
        G≡H = case G H Gff Gtt

    app≡ : ∀ {W A B} {φ ψ : Hom W (Exp A B)} (a : Hom W A) → φ ≡ ψ → app φ a ≡ app ψ a
    app≡ a refl = refl

    -- step commutes with pointwise ∧
    step-andE : ∀ {W} (φ ψ : Hom W E) →
                andE ∘ ⟨ step ∘ φ , step ∘ ψ ⟩ ≡ step ∘ (andE ∘ ⟨ φ , ψ ⟩)
    step-andE φ ψ =
      ext _ _
        (app ((andE ∘ ⟨ step ∘ φ , step ∘ ψ ⟩) ∘ π₁) π₂
           ≡⟨ app≡ π₂ (trans (assoc _ _ _) (∘r andE (trans (⟨⟩-∘ _ _ _)
                (pair≡ (assoc _ _ _) (assoc _ _ _))))) ⟩
         app (andE ∘ ⟨ step ∘ (φ ∘ π₁) , step ∘ (ψ ∘ π₁) ⟩) π₂
           ≡⟨ app-andE _ _ _ ⟩
         app (step ∘ (φ ∘ π₁)) π₂ ∧ app (step ∘ (ψ ∘ π₁)) π₂
           ≡⟨ ∧-cong (app-step _ _) (app-step _ _) ⟩
         K ∘ ⟨ c ∘ π₂ , φ ∘ π₁ ⟩ ∧ K ∘ ⟨ c ∘ π₂ , ψ ∘ π₁ ⟩
           ≡⟨ step-∧ _ _ _ ⟩
         K ∘ ⟨ c ∘ π₂ , andE ∘ ⟨ φ ∘ π₁ , ψ ∘ π₁ ⟩ ⟩
           ≡⟨ sym (app-step _ _) ⟩
         app (step ∘ (andE ∘ ⟨ φ ∘ π₁ , ψ ∘ π₁ ⟩)) π₂
           ≡⟨ app≡ π₂ (∘r step (trans (∘r andE (sym (⟨⟩-∘ _ _ _))) (sym (assoc _ _ _)))) ⟩
         app (step ∘ ((andE ∘ ⟨ φ , ψ ⟩) ∘ π₁)) π₂
           ≡⟨ app≡ π₂ (sym (assoc _ _ _)) ⟩
         app ((step ∘ (andE ∘ ⟨ φ , ψ ⟩)) ∘ π₁) π₂ ∎)

    -- χ(x) ∧ [ff, φ](c x) = [ff, φ](c x), generically in z = c x
    isinr : Hom (𝟙 + C) 𝟚
    isinr = [ ι₁ , ι₂ ∘ ! ]

    base-gen : ∀ {W} (z : Hom W (𝟙 + C)) (φ : Hom W E) →
               (isinr ∘ z) ∧ K ∘ ⟨ z , φ ⟩ ≡ K ∘ ⟨ z , φ ⟩
    base-gen z φ =
      trans (sym gen) (trans (∘l _ G≡H) (trans (assoc _ _ _) (∘r K (trans (∘l _ pair-id) (idl _)))))
      where
        G : Hom ((𝟙 + C) × E) 𝟚
        G = (isinr ∘ π₁) ∧ K
        gen : G ∘ ⟨ z , φ ⟩ ≡ (isinr ∘ z) ∧ K ∘ ⟨ z , φ ⟩
        gen = trans (∧-∘ _ _ _)
                (∧-cong (trans (assoc _ _ _) (∘r isinr (π₁-β _ _)))
                        refl)
        Gff : G ∘ (ι₁ ⊠ id) ≡ K ∘ (ι₁ ⊠ id)
        Gff =
          trans (∧-∘ _ _ _)
            (trans (∧-cong (trans (assoc _ _ _)
                              (trans (∘r isinr (π₁-β _ _))
                                (trans (sym (assoc _ _ _))
                                  (trans (∘l π₁ (ι₁-β _ _)) (∘r ι₁ (!-uni π₁))))))
                           refl)
              (trans (ff-∧ _) (sym (cases-β₁ _ _))))
        Gtt : G ∘ (ι₂ ⊠ id) ≡ K ∘ (ι₂ ⊠ id)
        Gtt =
          trans (∧-∘ _ _ _)
            (trans (∧-cong (trans (assoc _ _ _)
                              (trans (∘r isinr (π₁-β _ _))
                                (trans (sym (assoc _ _ _))
                                  (trans (∘l π₁ (ι₂-β _ _)) (trans (assoc _ _ _) (∘r ι₂ (!-uni _)))))))
                           refl)
              (tt-∧ _))
        G≡H : G ≡ K ∘ ⟨ π₁ , π₂ ⟩
        G≡H = trans (case G K Gff Gtt) (sym (trans (∘r K pair-id) (idr K)))

    -- (A) r(n+1) = r(n) ∧ r(n+1)
    r-dec : r ∘ suc ≡ andE ∘ ⟨ r , r ∘ suc ⟩
    r-dec = trans (it-uni x₁ step (r ∘ suc) f0 fs)
                  (sym (it-uni x₁ step (andE ∘ ⟨ r , r ∘ suc ⟩) g0 gs))
      where
        x₁ : Hom 𝟙 E
        x₁ = step ∘ χ̂
        rs : r ∘ suc ≡ step ∘ r
        rs = it-s χ̂ step
        rz : r ∘ zero ≡ χ̂
        rz = it-z χ̂ step
        f0 : (r ∘ suc) ∘ zero ≡ x₁
        f0 = trans (∘l zero rs) (trans (assoc _ _ _) (∘r step rz))
        fs : (r ∘ suc) ∘ suc ≡ step ∘ (r ∘ suc)
        fs = trans (∘l suc rs) (assoc _ _ _)
        g0 : (andE ∘ ⟨ r , r ∘ suc ⟩) ∘ zero ≡ x₁
        g0 =
          (andE ∘ ⟨ r , r ∘ suc ⟩) ∘ zero
            ≡⟨ trans (assoc _ _ _) (∘r andE (trans (⟨⟩-∘ _ _ _) (pair≡ rz f0))) ⟩
          andE ∘ ⟨ χ̂ , x₁ ⟩
            ≡⟨ ext _ _ pt ⟩
          x₁ ∎
          where
            χ̂π : app (χ̂ ∘ π₁) π₂ ≡ isinr ∘ (c ∘ π₂)
            χ̂π = trans (app-lam _ _ _)
                   (trans (assoc _ _ _) (trans (∘r χ (π₂-β _ _)) (assoc _ _ _)))
            pt : app ((andE ∘ ⟨ χ̂ , x₁ ⟩) ∘ π₁) π₂ ≡ app (x₁ ∘ π₁) π₂
            pt =
              app ((andE ∘ ⟨ χ̂ , x₁ ⟩) ∘ π₁) π₂
                ≡⟨ app≡ π₂ (trans (assoc _ _ _) (∘r andE (⟨⟩-∘ _ _ _))) ⟩
              app (andE ∘ ⟨ χ̂ ∘ π₁ , x₁ ∘ π₁ ⟩) π₂
                ≡⟨ app-andE _ _ _ ⟩
              app (χ̂ ∘ π₁) π₂ ∧ app (x₁ ∘ π₁) π₂
                ≡⟨ ∧-cong χ̂π (trans (app≡ π₂ (assoc _ _ _)) (app-step _ _)) ⟩
              (isinr ∘ (c ∘ π₂)) ∧ K ∘ ⟨ c ∘ π₂ , χ̂ ∘ π₁ ⟩
                ≡⟨ base-gen _ _ ⟩
              K ∘ ⟨ c ∘ π₂ , χ̂ ∘ π₁ ⟩
                ≡⟨ sym (trans (app≡ π₂ (assoc _ _ _)) (app-step _ _)) ⟩
              app (x₁ ∘ π₁) π₂ ∎
        gs : (andE ∘ ⟨ r , r ∘ suc ⟩) ∘ suc ≡ step ∘ (andE ∘ ⟨ r , r ∘ suc ⟩)
        gs =
          (andE ∘ ⟨ r , r ∘ suc ⟩) ∘ suc
            ≡⟨ trans (assoc _ _ _) (∘r andE (trans (⟨⟩-∘ _ _ _)
                 (pair≡ rs (trans (∘l suc rs) (assoc _ _ _))))) ⟩
          andE ∘ ⟨ step ∘ r , step ∘ (r ∘ suc) ⟩
            ≡⟨ step-andE _ _ ⟩
          step ∘ (andE ∘ ⟨ r , r ∘ suc ⟩) ∎

    -- (B) the candidate, as a sequence-valued map and in M
    ĝ : Hom C S
    ĝ = lam (app (r ∘ π₂) π₁)

    app-ĝ : ∀ {W} (x : Hom W C) (n : Hom W N) → app (ĝ ∘ x) n ≡ app (r ∘ n) x
    app-ĝ x n =
      trans (app-lam _ _ _)
        (trans (app-∘ _ _ _)
          (cong₂ app (trans (assoc _ _ _) (∘r r (π₂-β _ _))) (π₁-β _ _)))

    ĝ-dec : ∀ {V} (h : Hom V C) (n : Hom V N) →
            app (ĝ ∘ h) (suc ∘ n) ≡ app (ĝ ∘ h) n ∧ app (ĝ ∘ h) (suc ∘ n)
    ĝ-dec h n =
      app (ĝ ∘ h) (suc ∘ n)
        ≡⟨ app-ĝ _ _ ⟩
      app (r ∘ (suc ∘ n)) h
        ≡⟨ app≡ h (trans (sym (assoc _ _ _)) (trans (∘l n r-dec)
             (trans (assoc _ _ _) (∘r andE (trans (⟨⟩-∘ _ _ _) (pair≡ refl (assoc _ _ _))))))) ⟩
      app (andE ∘ ⟨ r ∘ n , r ∘ (suc ∘ n) ⟩) h
        ≡⟨ app-andE _ _ _ ⟩
      app (r ∘ n) h ∧ app (r ∘ (suc ∘ n)) h
        ≡⟨ sym (∧-cong (app-ĝ _ _) (app-ĝ _ _)) ⟩
      app (ĝ ∘ h) n ∧ app (ĝ ∘ h) (suc ∘ n) ∎

    ĝM : Hom C M
    ĝM = fact ĝ (intoM ĝ ĝ-dec)

    m-ĝM : m ∘ ĝM ≡ ĝ
    m-ĝM = fact-β _ _

    -- the shifted sequence, computed by cases on c
    shift-gen : ∀ (v : Hom C S) (Γ : Hom N E) →
                (∀ {W} (y : Hom W C) (n : Hom W N) → app (v ∘ y) n ≡ app (Γ ∘ n) y) →
                ∀ {W} (x : Hom W C) (n : Hom W N) →
                app ([ zeroS , v ] ∘ (c ∘ x)) n ≡ K ∘ ⟨ c ∘ x , Γ ∘ n ⟩
    shift-gen v Γ hyp x n =
      trans (sym (trans (app-∘ _ _ _)
                   (cong₂ app (trans (assoc _ _ _) (∘r _ (π₁-β _ _))) (π₂-β _ _))))
        (trans (∘l _ L≡R)
          (trans (assoc _ _ _)
            (∘r K (trans (⟨⟩-∘ _ _ _)
                    (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (∘r Γ (π₂-β _ _))))))))
      where
        Q = (𝟙 + C) × N
        L R : Hom Q 𝟚
        L = app ([ zeroS , v ] ∘ π₁) π₂
        R = K ∘ ⟨ π₁ , Γ ∘ π₂ ⟩
        atR : ∀ {B} (i : Hom B (𝟙 + C)) → ⟨ π₁ , Γ ∘ π₂ ⟩ ∘ (i ⊠ id) ≡ ⟨ i ∘ π₁ , Γ ∘ π₂ ⟩
        atR i = trans (⟨⟩-∘ _ _ _)
                  (pair≡ (π₁-β _ _) (trans (assoc _ _ _) (∘r Γ (trans (π₂-β _ _) (idl π₂)))))
        atL : ∀ {B} (i : Hom B (𝟙 + C)) (w : Hom B S) → [ zeroS , v ] ∘ i ≡ w →
              L ∘ (i ⊠ id) ≡ app (w ∘ π₁) π₂
        atL i w e =
          trans (app-∘ _ _ _)
            (cong₂ app (trans (assoc _ _ _)
                          (trans (∘r _ (π₁-β _ _)) (trans (sym (assoc _ _ _)) (∘l π₁ e))))
                       (trans (π₂-β _ _) (idl π₂)))
        Lff : L ∘ (ι₁ ⊠ id) ≡ R ∘ (ι₁ ⊠ id)
        Lff =
          trans (atL ι₁ zeroS (ι₁-β _ _))
            (trans (app-zeroS-∘ _ _)
              (sym (trans (assoc _ _ _)
                     (trans (∘r K (atR ι₁))
                       (trans (∘r K (pair≡ (∘r ι₁ (!-uni π₁)) refl)) (K-ff _))))))
        Ltt : L ∘ (ι₂ ⊠ id) ≡ R ∘ (ι₂ ⊠ id)
        Ltt =
          trans (atL ι₂ v (ι₂-β _ _))
            (trans (hyp π₁ π₂)
              (sym (trans (assoc _ _ _) (trans (∘r K (atR ι₂)) (K-in _ _)))))
        L≡R : L ≡ R
        L≡R = case L R Lff Ltt

    pred-ĝM : pred ∘ ĝM ≡ [ zeroM , ĝM ] ∘ c
    pred-ĝM =
      eqm-mono _ _
        (trans (sym (assoc _ _ _))
          (trans (∘l ĝM m-pred)
            (trans (assoc _ _ _)
              (trans (∘r shift m-ĝM)
                (trans (ext _ _ pt)
                  (sym (trans (sym (assoc _ _ _))
                         (trans (∘l c ([]-∘ m zeroM ĝM))
                           (∘l c (cong₂ [_,_] m-zeroM m-ĝM))))))))))
      where
        pt : app ((shift ∘ ĝ) ∘ π₁) π₂ ≡ app (([ zeroS , ĝ ] ∘ c) ∘ π₁) π₂
        pt =
          app ((shift ∘ ĝ) ∘ π₁) π₂
            ≡⟨ trans (app≡ π₂ (assoc _ _ _)) (app-shift _ _) ⟩
          app (ĝ ∘ π₁) (suc ∘ π₂)
            ≡⟨ app-ĝ _ _ ⟩
          app (r ∘ (suc ∘ π₂)) π₁
            ≡⟨ app≡ π₁ (trans (sym (assoc _ _ _)) (trans (∘l π₂ (it-s χ̂ step)) (assoc _ _ _))) ⟩
          app (step ∘ (r ∘ π₂)) π₁
            ≡⟨ app-step _ _ ⟩
          K ∘ ⟨ c ∘ π₁ , r ∘ π₂ ⟩
            ≡⟨ sym (shift-gen ĝ r app-ĝ π₁ π₂) ⟩
          app ([ zeroS , ĝ ] ∘ (c ∘ π₁)) π₂
            ≡⟨ app≡ π₂ (sym (assoc _ _ _)) ⟩
          app (([ zeroS , ĝ ] ∘ c) ∘ π₁) π₂ ∎

    head-ĝM : head ∘ ĝM ≡ χ
    head-ĝM =
      head ∘ ĝM
        ≡⟨ app-∘ _ _ _ ⟩
      app (m ∘ ĝM) ((zero ∘ !) ∘ ĝM)
        ≡⟨ cong₂ app m-ĝM (trans (assoc _ _ _) (∘r zero (!-∘ _))) ⟩
      app ĝ (zero ∘ !)
        ≡⟨ app≡ _ (sym (idr ĝ)) ⟩
      app (ĝ ∘ id) (zero ∘ !)
        ≡⟨ app-ĝ _ _ ⟩
      app (r ∘ (zero ∘ !)) id
        ≡⟨ app≡ id (trans (sym (assoc _ _ _)) (∘l ! (it-z χ̂ step))) ⟩
      app (χ̂ ∘ !) id
        ≡⟨ app-lam _ _ _ ⟩
      (χ ∘ π₂) ∘ ⟨ ! , id ⟩
        ≡⟨ trans (assoc _ _ _) (trans (∘r χ (π₂-β _ _)) (idr χ)) ⟩
      χ ∎

    -- (F) existence
    corec : Hom C M
    corec = ĝM

    out-gen : ∀ (h : Hom C M) →
              cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ ⟨ isinr , [ zeroM , h ] ⟩ ≡ [ ι₁ , ι₂ ∘ h ]
    out-gen h =
      copair-uni _ _
        (trans (assoc _ _ _)
          (trans (∘r _ (trans (⟨⟩-∘ _ _ _) (pair≡ (ι₁-β _ _) (ι₁-β _ _))))
            (trans (∘r _ (pair≡ (trans (sym (idr ι₁)) (∘r ι₁ (!-uni id))) refl))
              (trans (cases-at₁ _ _ _ _)
                (trans (assoc _ _ _)
                  (trans (∘r ι₁ (𝟙-pt _)) (trans (idr ι₁) (sym (ι₁-β _ _)))))))))
        (trans (assoc _ _ _)
          (trans (∘r _ (trans (⟨⟩-∘ _ _ _) (pair≡ (ι₂-β _ _) (ι₂-β _ _))))
            (trans (cases-at₂ _ _ _ _)
              (trans (assoc _ _ _)
                (trans (∘r ι₂ (π₂-β _ _)) (sym (ι₂-β _ _)))))))

    corec-mor : IsMor corec
    corec-mor =
      out ∘ ĝM
        ≡⟨ trans (assoc _ _ _) (∘r _ (⟨⟩-∘ _ _ _)) ⟩
      cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ ⟨ head ∘ ĝM , pred ∘ ĝM ⟩
        ≡⟨ ∘r _ (pair≡ head-ĝM pred-ĝM) ⟩
      cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ ⟨ isinr ∘ c , [ zeroM , ĝM ] ∘ c ⟩
        ≡⟨ ∘r _ (sym (⟨⟩-∘ _ _ _)) ⟩
      cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ (⟨ isinr , [ zeroM , ĝM ] ⟩ ∘ c)
        ≡⟨ sym (assoc _ _ _) ⟩
      (cases (ι₁ ∘ !) (ι₂ ∘ π₂) ∘ ⟨ isinr , [ zeroM , ĝM ] ⟩) ∘ c
        ≡⟨ ∘l c (out-gen ĝM) ⟩
      [ ι₁ , ι₂ ∘ ĝM ] ∘ c ∎

    -- (G) uniqueness: every coalgebra map into M is corec
    module _ (g : Hom C M) (pg : IsMor g) where
      private
        hd : head ∘ g ≡ χ
        hd =
          head ∘ g
            ≡⟨ ∘l g (sym σ-out) ⟩
          (σ ∘ out) ∘ g
            ≡⟨ assoc _ _ _ ⟩
          σ ∘ (out ∘ g)
            ≡⟨ ∘r σ pg ⟩
          σ ∘ ([ ι₁ , ι₂ ∘ g ] ∘ c)
            ≡⟨ sym (assoc _ _ _) ⟩
          (σ ∘ [ ι₁ , ι₂ ∘ g ]) ∘ c
            ≡⟨ ∘l c (trans ([]-∘ σ ι₁ (ι₂ ∘ g))
                  (cong₂ [_,_] (ι₁-β _ _)
                    (trans (sym (assoc _ _ _))
                      (trans (∘l g (ι₂-β _ _)) (trans (assoc _ _ _) (∘r ι₂ (!-∘ g))))))) ⟩
          χ ∎

        pd : pred ∘ g ≡ [ zeroM , g ] ∘ c
        pd =
          pred ∘ g
            ≡⟨ ∘l g (sym τ-out) ⟩
          (τ ∘ out) ∘ g
            ≡⟨ assoc _ _ _ ⟩
          τ ∘ (out ∘ g)
            ≡⟨ ∘r τ pg ⟩
          τ ∘ ([ ι₁ , ι₂ ∘ g ] ∘ c)
            ≡⟨ sym (assoc _ _ _) ⟩
          (τ ∘ [ ι₁ , ι₂ ∘ g ]) ∘ c
            ≡⟨ ∘l c (trans ([]-∘ τ ι₁ (ι₂ ∘ g))
                  (cong₂ [_,_] (ι₁-β _ _)
                    (trans (sym (assoc _ _ _)) (trans (∘l g (ι₂-β _ _)) (idl g))))) ⟩
          [ zeroM , g ] ∘ c ∎

        v : Hom C S
        v = m ∘ g

        G : Hom N E
        G = lam (app (v ∘ π₂) π₁)

        appG : ∀ {W} (y : Hom W C) (n : Hom W N) → app (v ∘ y) n ≡ app (G ∘ n) y
        appG y n =
          sym (trans (app-lam _ _ _)
                (trans (app-∘ _ _ _)
                  (cong₂ app (trans (assoc _ _ _) (∘r v (π₂-β _ _))) (π₁-β _ _))))

        mpg : (shift ∘ m) ∘ g ≡ [ zeroS , v ] ∘ c
        mpg =
          trans (∘l g (sym m-pred))
            (trans (assoc _ _ _)
              (trans (∘r m pd)
                (trans (sym (assoc _ _ _))
                  (∘l c (trans ([]-∘ m zeroM g) (cong₂ [_,_] m-zeroM refl))))))

        G0 : G ∘ zero ≡ χ̂
        G0 = ext _ _
          (app ((G ∘ zero) ∘ π₁) π₂
             ≡⟨ trans (app≡ π₂ (assoc _ _ _)) (sym (appG _ _)) ⟩
           app (v ∘ π₂) (zero ∘ π₁)
             ≡⟨ app≡ _ (assoc _ _ _) ⟩
           app (m ∘ (g ∘ π₂)) (zero ∘ π₁)
             ≡⟨ cong (app (m ∘ (g ∘ π₂)))
                  (trans (∘r zero (!-uni π₁))
                    (sym (trans (assoc _ _ _) (∘r zero (!-∘ _))))) ⟩
           app (m ∘ (g ∘ π₂)) ((zero ∘ !) ∘ (g ∘ π₂))
             ≡⟨ sym (app-∘ _ _ _) ⟩
           head ∘ (g ∘ π₂)
             ≡⟨ trans (sym (assoc _ _ _)) (∘l π₂ hd) ⟩
           χ ∘ π₂
             ≡⟨ sym (trans (app-lam _ _ _) (trans (assoc _ _ _) (∘r χ (π₂-β _ _)))) ⟩
           app (χ̂ ∘ π₁) π₂ ∎)

        Gs : G ∘ suc ≡ step ∘ G
        Gs = ext _ _
          (app ((G ∘ suc) ∘ π₁) π₂
             ≡⟨ trans (app≡ π₂ (assoc _ _ _)) (sym (appG _ _)) ⟩
           app (v ∘ π₂) (suc ∘ π₁)
             ≡⟨ app≡ _ (assoc _ _ _) ⟩
           app (m ∘ (g ∘ π₂)) (suc ∘ π₁)
             ≡⟨ sym (app-shift _ _) ⟩
           app (shift ∘ (m ∘ (g ∘ π₂))) π₁
             ≡⟨ app≡ π₁ (trans (sym (assoc _ _ _))
                  (trans (sym (assoc _ _ _)) (trans (∘l π₂ mpg) (assoc _ _ _)))) ⟩
           app ([ zeroS , v ] ∘ (c ∘ π₂)) π₁
             ≡⟨ shift-gen v G appG π₂ π₁ ⟩
           K ∘ ⟨ c ∘ π₂ , G ∘ π₁ ⟩
             ≡⟨ sym (trans (app≡ π₂ (assoc _ _ _)) (app-step _ _)) ⟩
           app ((step ∘ G) ∘ π₁) π₂ ∎)

        G≡r : G ≡ r
        G≡r = it-uni χ̂ step G G0 Gs

        v≡ĝ : v ≡ ĝ
        v≡ĝ = ext _ _
          (app (v ∘ π₁) π₂
             ≡⟨ appG _ _ ⟩
           app (G ∘ π₂) π₁
             ≡⟨ app≡ π₁ (∘l π₂ G≡r) ⟩
           app (r ∘ π₂) π₁
             ≡⟨ sym (app-ĝ _ _) ⟩
           app (ĝ ∘ π₁) π₂ ∎)

      corec-uni : g ≡ corec
      corec-uni = eqm-mono _ _ (trans v≡ĝ (sym m-ĝM))
