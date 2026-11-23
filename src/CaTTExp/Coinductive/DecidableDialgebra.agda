------------------------------------------------------------------------
-- Ledger F12c / F12d (notes/coinductive.md §4, "Internal labels:
-- decidable families"; notes/descent-vs-init.md §5b).
--
-- Terminal dialgebras for decidable families, from universality of the
-- coproduct 2 = 1 + 1 (U-⊔) and terminal constant-arity machines.
--
-- Setting: the record `Cat⁺` below, a category with strict (≡)
-- equations, a terminal object, binary products, binary coproducts and
-- equalisers, together with
--   (U-⊔ at 2)  for every φ : Y → 2, the comparison
--               [eqm, eqm] : Eq φ tt + Eq φ ff → Y  is invertible
-- (the instance of U-⊔ for f = φ : Y → 1 + 1, the pullbacks of the
-- two points being the equalisers with the constant maps).  No
-- disjointness, no exponentials, no NNO.
--
-- A *decidable B-family* is given by χ : A × B → 2; its total object is
-- E = Eq χ tt ⊆ A × B and p = π₁ ∘ eqm : E → A.  Fin → ℕ is the case
-- A = B = ℕ, χ(n, i) = (i < n).
--
-- Machine-checked (no postulates):
--   * `Dom h` (the tt-part of C × B under χ ∘ (h × B)) is a pullback of
--     p along h (`dom-pb`, `dom-pb-C`, `dom-pb-E`, `dom-pb-uni`), so the
--     dialgebras `Dial` below are exactly p-dialgebras (C, h, t : C ×_A E → C);
--   * `Final.terminal` / `Final.unique`: ASSUMING a terminal machine
--     (C, h, s : C × B → C) — the constant-arity result, Known 1 /
--     notes/coinductive.md §2, formalised for the biclosed interface in
--     CaTTExp.Coinductive.ConstArity, taken here as a module parameter —
--     the dialgebras have a terminal object.  Proof: extend each
--     transition by "stay" using U-⊔ (`J₀`), map to the terminal machine
--     (`η`), and take the equaliser of id and the idempotent η_X.
--
-- Scope and honesty notes.
--   * 1-categorical with strict equality of morphisms (the 1-truncated
--     shadow).  The system-level transfer (set labels, L-×) is argued in
--     the notes, not encoded.
--   * The terminal machine is a hypothesis, not constructed here.
--   * The product is cartesian (⊗ = ×).
------------------------------------------------------------------------
module CaTTExp.Coinductive.DecidableDialgebra where

open import CaTTExp.Prelude using (_≡_; refl; sym; trans; cong; cong₂)
open import CaTTExp.Descent.CocartLemmas using (_≡⟨_⟩_; _∎)

record Cat⁺ : Set₁ where
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

    -- U-⊔ at 2 = 1 + 1: the comparison out of the sum of the two
    -- pullbacks (the equalisers with the constant maps ι₁ ∘ !, ι₂ ∘ !)
    -- is invertible
    split   : ∀ {Y} (φ : Hom Y (𝟙 + 𝟙)) → Hom Y (Eq φ (ι₁ ∘ !) + Eq φ (ι₂ ∘ !))
    split-l : ∀ {Y} (φ : Hom Y (𝟙 + 𝟙)) → [ eqm , eqm ] ∘ split φ ≡ id
    split-r : ∀ {Y} (φ : Hom Y (𝟙 + 𝟙)) → split φ ∘ [ eqm , eqm ] ≡ id

  -- the two points of 2 = 1 + 1, as constant maps
  TT FF : ∀ {Y} → Hom Y (𝟙 + 𝟙)
  TT = ι₁ ∘ !
  FF = ι₂ ∘ !

module Theory (𝒞 : Cat⁺) where
  open Cat⁺ 𝒞

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
    trans (sym (⟨⟩-η _))
      (pair≡ (trans (sym (assoc _ _ _)) (∘l h (π₁-β f g)))
             (trans (sym (assoc _ _ _)) (∘l h (π₂-β f g))))

  pair-uni : ∀ {W A B} (h h′ : Hom W (A × B)) →
             π₁ ∘ h ≡ π₁ ∘ h′ → π₂ ∘ h ≡ π₂ ∘ h′ → h ≡ h′
  pair-uni h h′ e₁ e₂ = trans (sym (⟨⟩-η h)) (trans (pair≡ e₁ e₂) (⟨⟩-η h′))

  copair-∘ : ∀ {A B Y Z} (k : Hom Y Z) (f : Hom A Y) (g : Hom B Y) →
             k ∘ [ f , g ] ≡ [ k ∘ f , k ∘ g ]
  copair-∘ k f g =
    trans (sym ([]-η _))
      (cong₂ [_,_] (trans (assoc _ _ _) (∘r k (ι₁-β f g)))
                   (trans (assoc _ _ _) (∘r k (ι₂-β f g))))

  const-∘ : ∀ {V W} (k : Hom V W) {i : Hom 𝟙 (𝟙 + 𝟙)} → (i ∘ !) ∘ k ≡ i ∘ !
  const-∘ k {i} = trans (assoc _ _ _) (∘r i (!-uni _))

  -- f ⊠ B = f × id_B
  _⊠ : ∀ {C D B} → Hom C D → Hom (C × B) (D × B)
  f ⊠ = ⟨ f ∘ π₁ , π₂ ⟩

  ⊠-∘ : ∀ {C D F B} (g : Hom D F) (f : Hom C D) →
        _⊠ {B = B} g ∘ (f ⊠) ≡ (g ∘ f) ⊠
  ⊠-∘ g f =
    trans (⟨⟩-∘ _ _ _)
      (pair≡ (trans (assoc _ _ _) (trans (∘r g (π₁-β _ _)) (sym (assoc _ _ _))))
             (π₂-β _ _))

  π₁-⊠ : ∀ {C D B} (f : Hom C D) → π₁ ∘ _⊠ {B = B} f ≡ f ∘ π₁
  π₁-⊠ f = π₁-β _ _

  -- the two summands of the comparison
  split-tt : ∀ {Y} (φ : Hom Y (𝟙 + 𝟙)) → split φ ∘ eqm {f = φ} {TT} ≡ ι₁
  split-tt φ =
    trans (∘r (split φ) (sym (ι₁-β eqm eqm)))
      (trans (sym (assoc _ _ _)) (trans (∘l ι₁ (split-r φ)) (idl ι₁)))

  split-ff : ∀ {Y} (φ : Hom Y (𝟙 + 𝟙)) → split φ ∘ eqm {f = φ} {FF} ≡ ι₂
  split-ff φ =
    trans (∘r (split φ) (sym (ι₂-β eqm eqm)))
      (trans (sym (assoc _ _ _)) (trans (∘l ι₂ (split-r φ)) (idl ι₂)))

  -- maps out of Y agree if they agree on both parts
  by-parts : ∀ {Y Z} (φ : Hom Y (𝟙 + 𝟙)) (u v : Hom Y Z) →
             u ∘ eqm {f = φ} {TT} ≡ v ∘ eqm → u ∘ eqm {f = φ} {FF} ≡ v ∘ eqm → u ≡ v
  by-parts φ u v et ef =
    u                                  ≡⟨ sym (idr u) ⟩
    u ∘ id                             ≡⟨ ∘r u (sym (split-l φ)) ⟩
    u ∘ ([ eqm , eqm ] ∘ split φ)      ≡⟨ sym (assoc _ _ _) ⟩
    (u ∘ [ eqm , eqm ]) ∘ split φ      ≡⟨ ∘l (split φ) (trans (copair-∘ u _ _)
                                             (trans (cong₂ [_,_] et ef) (sym (copair-∘ v _ _)))) ⟩
    (v ∘ [ eqm , eqm ]) ∘ split φ      ≡⟨ assoc _ _ _ ⟩
    v ∘ ([ eqm , eqm ] ∘ split φ)      ≡⟨ ∘r v (split-l φ) ⟩
    v ∘ id                             ≡⟨ idr v ⟩
    v ∎

------------------------------------------------------------------------
-- Dialgebras of a decidable family χ : A × B → 2

module Family (𝒞 : Cat⁺) {A B : Cat⁺.Ob 𝒞} (χ : Cat⁺.Hom 𝒞 (Cat⁺._×_ 𝒞 A B) (Cat⁺._+_ 𝒞 (Cat⁺.𝟙 𝒞) (Cat⁺.𝟙 𝒞))) where
  open Cat⁺ 𝒞
  open Theory 𝒞

  φ : ∀ {C} → Hom C A → Hom (C × B) (𝟙 + 𝟙)
  φ h = χ ∘ (h ⊠)

  Dom Off : ∀ {C} → Hom C A → Ob
  Dom h = Eq (φ h) TT
  Off h = Eq (φ h) FF

  φ-nat : ∀ {C D} (h′ : Hom D A) (g : Hom C D) → φ h′ ∘ (g ⊠) ≡ φ (h′ ∘ g)
  φ-nat h′ g = trans (assoc _ _ _) (∘r χ (⊠-∘ h′ g))

  -- (g × B) restricted to the parts, for g over A
  liftT : ∀ {C D} {h : Hom C A} {h′ : Hom D A} (g : Hom C D) → h′ ∘ g ≡ h → Hom (Dom h) (Dom h′)
  liftT {h = h} {h′} g r =
    fact ((g ⊠) ∘ eqm)
      (trans (sym (assoc _ _ _))
        (trans (∘l eqm (trans (φ-nat h′ g) (cong φ r)))
          (trans eqm-eq (trans (const-∘ eqm) (sym (const-∘ _))))))

  liftF : ∀ {C D} {h : Hom C A} {h′ : Hom D A} (g : Hom C D) → h′ ∘ g ≡ h → Hom (Off h) (Off h′)
  liftF {h = h} {h′} g r =
    fact ((g ⊠) ∘ eqm)
      (trans (sym (assoc _ _ _))
        (trans (∘l eqm (trans (φ-nat h′ g) (cong φ r)))
          (trans eqm-eq (trans (const-∘ eqm) (sym (const-∘ _))))))

  m-liftT : ∀ {C D} {h : Hom C A} {h′ : Hom D A} (g : Hom C D) (r : h′ ∘ g ≡ h) →
            eqm ∘ liftT g r ≡ (g ⊠) ∘ eqm
  m-liftT g r = fact-β _ _

  m-liftF : ∀ {C D} {h : Hom C A} {h′ : Hom D A} (g : Hom C D) (r : h′ ∘ g ≡ h) →
            eqm ∘ liftF g r ≡ (g ⊠) ∘ eqm
  m-liftF g r = fact-β _ _

  lift-eq : ∀ {C D} {h : Hom C A} {h′ : Hom D A} (g g′ : Hom C D)
            (r : h′ ∘ g ≡ h) (r′ : h′ ∘ g′ ≡ h) → g ≡ g′ → liftT g r ≡ liftT g′ r′
  lift-eq g .g r r′ refl = eqm-mono _ _ (trans (m-liftT g r) (sym (m-liftT g r′)))

  lift-∘ : ∀ {C D F} {h : Hom C A} {h′ : Hom D A} {h″ : Hom F A}
           (g : Hom D F) (f : Hom C D) (r : h″ ∘ g ≡ h′) (s : h′ ∘ f ≡ h) (q : h″ ∘ (g ∘ f) ≡ h) →
           liftT g r ∘ liftT f s ≡ liftT (g ∘ f) q
  lift-∘ g f r s q =
    eqm-mono _ _
      (eqm ∘ (liftT g r ∘ liftT f s)      ≡⟨ sym (assoc _ _ _) ⟩
       (eqm ∘ liftT g r) ∘ liftT f s      ≡⟨ ∘l _ (m-liftT g r) ⟩
       ((g ⊠) ∘ eqm) ∘ liftT f s          ≡⟨ assoc _ _ _ ⟩
       (g ⊠) ∘ (eqm ∘ liftT f s)          ≡⟨ ∘r _ (m-liftT f s) ⟩
       (g ⊠) ∘ ((f ⊠) ∘ eqm)              ≡⟨ sym (assoc _ _ _) ⟩
       ((g ⊠) ∘ (f ⊠)) ∘ eqm              ≡⟨ ∘l eqm (⊠-∘ g f) ⟩
       ((g ∘ f) ⊠) ∘ eqm                  ≡⟨ sym (m-liftT _ q) ⟩
       eqm ∘ liftT (g ∘ f) q ∎)

  ----------------------------------------------------------------------
  -- Dom h is the pullback C ×_A E, with E = Eq χ TT and p = π₁ ∘ eqm.

  E : Ob
  E = Eq χ TT

  p : Hom E A
  p = π₁ ∘ eqm

  module _ {C : Ob} (h : Hom C A) where

    dom-C : Hom (Dom h) C
    dom-C = π₁ ∘ eqm

    dom-E : Hom (Dom h) E
    dom-E = fact ((h ⊠) ∘ eqm)
              (trans (sym (assoc _ _ _))
                (trans eqm-eq (trans (const-∘ eqm) (sym (const-∘ _)))))

    dom-sq : h ∘ dom-C ≡ p ∘ dom-E
    dom-sq =
      sym (trans (assoc _ _ _)
            (trans (∘r π₁ (fact-β _ _))
              (trans (sym (assoc _ _ _))
                (trans (∘l eqm (π₁-⊠ h)) (assoc _ _ _)))))

    dom-pb : ∀ {Z} (x : Hom Z C) (y : Hom Z E) → h ∘ x ≡ p ∘ y → Hom Z (Dom h)
    dom-pb x y w =
      fact ⟨ x , π₂ ∘ (eqm ∘ y) ⟩
        (φ h ∘ ⟨ x , π₂ ∘ (eqm ∘ y) ⟩                ≡⟨ assoc _ _ _ ⟩
         χ ∘ ((h ⊠) ∘ ⟨ x , π₂ ∘ (eqm ∘ y) ⟩)        ≡⟨ ∘r χ (trans (⟨⟩-∘ _ _ _)
                                                        (pair≡ (trans (assoc _ _ _) (∘r h (π₁-β _ _)))
                                                               (π₂-β _ _))) ⟩
         χ ∘ ⟨ h ∘ x , π₂ ∘ (eqm ∘ y) ⟩              ≡⟨ ∘r χ (trans (pair≡ (trans w (assoc _ _ _)) refl)
                                                        (⟨⟩-η _)) ⟩
         χ ∘ (eqm ∘ y)                               ≡⟨ sym (assoc _ _ _) ⟩
         (χ ∘ eqm) ∘ y                               ≡⟨ ∘l y eqm-eq ⟩
         (TT ∘ eqm) ∘ y                              ≡⟨ trans (∘l y (const-∘ eqm)) (trans (const-∘ y) (sym (const-∘ _))) ⟩
         TT ∘ ⟨ x , π₂ ∘ (eqm ∘ y) ⟩ ∎)

    dom-pb-C : ∀ {Z} (x : Hom Z C) (y : Hom Z E) (w : h ∘ x ≡ p ∘ y) →
               dom-C ∘ dom-pb x y w ≡ x
    dom-pb-C x y w = trans (assoc _ _ _) (trans (∘r π₁ (fact-β _ _)) (π₁-β _ _))

    dom-pb-E : ∀ {Z} (x : Hom Z C) (y : Hom Z E) (w : h ∘ x ≡ p ∘ y) →
               dom-E ∘ dom-pb x y w ≡ y
    dom-pb-E x y w =
      eqm-mono _ _
        (trans (sym (assoc _ _ _))
          (trans (∘l _ (fact-β _ _))
            (trans (assoc _ _ _)
              (trans (∘r _ (fact-β _ _))
                (trans (⟨⟩-∘ _ _ _)
                  (trans (pair≡ (trans (assoc _ _ _) (trans (∘r h (π₁-β _ _)) (trans w (assoc _ _ _))))
                                (π₂-β _ _))
                    (⟨⟩-η _)))))))

    π₂-dom : π₂ ∘ eqm {f = φ h} {TT} ≡ (π₂ ∘ eqm) ∘ dom-E
    π₂-dom =
      π₂ ∘ eqm                      ≡⟨ ∘l eqm (sym (π₂-β _ _)) ⟩
      (π₂ ∘ (h ⊠)) ∘ eqm            ≡⟨ assoc _ _ _ ⟩
      π₂ ∘ ((h ⊠) ∘ eqm)            ≡⟨ ∘r π₂ (sym (fact-β _ _)) ⟩
      π₂ ∘ (eqm ∘ dom-E)            ≡⟨ sym (assoc _ _ _) ⟩
      (π₂ ∘ eqm) ∘ dom-E ∎

    dom-pb-uni : ∀ {Z} (u v : Hom Z (Dom h)) →
                 dom-C ∘ u ≡ dom-C ∘ v → dom-E ∘ u ≡ dom-E ∘ v → u ≡ v
    dom-pb-uni u v eC eE =
      eqm-mono u v
        (pair-uni _ _
          (trans (sym (assoc _ _ _)) (trans eC (assoc _ _ _)))
          (trans (sw u) (trans (∘r (π₂ ∘ eqm) eE) (sym (sw v)))))
      where
        sw : ∀ (w : Hom _ (Dom h)) → π₂ ∘ (eqm ∘ w) ≡ (π₂ ∘ eqm) ∘ (dom-E ∘ w)
        sw w = trans (sym (assoc _ _ _)) (trans (∘l w π₂-dom) (assoc _ _ _))

  ----------------------------------------------------------------------
  -- Dialgebras and machines

  record Dial : Set where
    field
      C : Ob
      h : Hom C A
      t : Hom (Dom h) C
  open Dial

  record DHom (D D′ : Dial) : Set where
    field
      map  : Hom (C D) (C D′)
      root : h D′ ∘ map ≡ h D
      step : map ∘ t D ≡ t D′ ∘ liftT map root
  open DHom

  dcomp : ∀ {D D′ D″} → DHom D′ D″ → DHom D D′ → DHom D D″
  map  (dcomp g f) = map g ∘ map f
  root (dcomp g f) = trans (sym (assoc _ _ _)) (trans (∘l (map f) (root g)) (root f))
  step (dcomp {D} {D′} {D″} g f) =
    (map g ∘ map f) ∘ t D                  ≡⟨ assoc _ _ _ ⟩
    map g ∘ (map f ∘ t D)                  ≡⟨ ∘r (map g) (step f) ⟩
    map g ∘ (t D′ ∘ liftT (map f) (root f)) ≡⟨ sym (assoc _ _ _) ⟩
    (map g ∘ t D′) ∘ liftT (map f) (root f) ≡⟨ ∘l _ (step g) ⟩
    (t D″ ∘ liftT (map g) (root g)) ∘ liftT (map f) (root f) ≡⟨ assoc _ _ _ ⟩
    t D″ ∘ (liftT (map g) (root g) ∘ liftT (map f) (root f)) ≡⟨ ∘r (t D″) (lift-∘ _ _ _ _ _) ⟩
    t D″ ∘ liftT (map g ∘ map f) _ ∎

  record Mach : Set where
    field
      MC : Ob
      mh : Hom MC A
      s  : Hom (MC × B) MC
  open Mach

  record MHom (M M′ : Mach) : Set where
    field
      mmap  : Hom (MC M) (MC M′)
      mroot : mh M′ ∘ mmap ≡ mh M
      mstep : mmap ∘ s M ≡ s M′ ∘ (mmap ⊠)
  open MHom

  mcomp : ∀ {M M′ M″} → MHom M′ M″ → MHom M M′ → MHom M M″
  mmap  (mcomp g f) = mmap g ∘ mmap f
  mroot (mcomp g f) = trans (sym (assoc _ _ _)) (trans (∘l (mmap f) (mroot g)) (mroot f))
  mstep (mcomp {M} {M′} {M″} g f) =
    (mmap g ∘ mmap f) ∘ s M            ≡⟨ assoc _ _ _ ⟩
    mmap g ∘ (mmap f ∘ s M)            ≡⟨ ∘r _ (mstep f) ⟩
    mmap g ∘ (s M′ ∘ (mmap f ⊠))       ≡⟨ sym (assoc _ _ _) ⟩
    (mmap g ∘ s M′) ∘ (mmap f ⊠)       ≡⟨ ∘l _ (mstep g) ⟩
    (s M″ ∘ (mmap g ⊠)) ∘ (mmap f ⊠)   ≡⟨ assoc _ _ _ ⟩
    s M″ ∘ ((mmap g ⊠) ∘ (mmap f ⊠))   ≡⟨ ∘r _ (⊠-∘ _ _) ⟩
    s M″ ∘ ((mmap g ∘ mmap f) ⊠) ∎

  -- the constant-arity result, assumed
  record TerminalMachine : Set where
    field
      T    : Mach
      term : ∀ M → MHom M T
      uni  : ∀ M (g : MHom M T) → mmap g ≡ mmap (term M)

  ----------------------------------------------------------------------
  -- J₀: extend the transition by "stay" on the ff-part (uses U-⊔)

  ext : (D : Dial) → Hom (C D × B) (C D)
  ext D = [ t D , π₁ ∘ eqm ] ∘ split (φ (h D))

  ext-tt : ∀ D → ext D ∘ eqm {f = φ (h D)} {TT} ≡ t D
  ext-tt D = trans (assoc _ _ _) (trans (∘r _ (split-tt _)) (ι₁-β _ _))

  ext-ff : ∀ D → ext D ∘ eqm {f = φ (h D)} {FF} ≡ π₁ ∘ eqm
  ext-ff D = trans (assoc _ _ _) (trans (∘r _ (split-ff _)) (ι₂-β _ _))

  J₀ : Dial → Mach
  MC (J₀ D) = C D
  mh (J₀ D) = h D
  s  (J₀ D) = ext D

  J₀-hom : ∀ {D D′} → DHom D D′ → MHom (J₀ D) (J₀ D′)
  mmap  (J₀-hom g) = map g
  mroot (J₀-hom g) = root g
  mstep (J₀-hom {D} {D′} g) =
    by-parts (φ (h D)) _ _
      ((map g ∘ ext D) ∘ eqm                   ≡⟨ assoc _ _ _ ⟩
       map g ∘ (ext D ∘ eqm)                   ≡⟨ ∘r _ (ext-tt D) ⟩
       map g ∘ t D                             ≡⟨ step g ⟩
       t D′ ∘ liftT (map g) (root g)           ≡⟨ ∘l _ (sym (ext-tt D′)) ⟩
       (ext D′ ∘ eqm) ∘ liftT (map g) (root g) ≡⟨ assoc _ _ _ ⟩
       ext D′ ∘ (eqm ∘ liftT (map g) (root g)) ≡⟨ ∘r _ (m-liftT _ _) ⟩
       ext D′ ∘ ((map g ⊠) ∘ eqm)              ≡⟨ sym (assoc _ _ _) ⟩
       (ext D′ ∘ (map g ⊠)) ∘ eqm ∎)
      ((map g ∘ ext D) ∘ eqm                   ≡⟨ assoc _ _ _ ⟩
       map g ∘ (ext D ∘ eqm)                   ≡⟨ ∘r _ (ext-ff D) ⟩
       map g ∘ (π₁ ∘ eqm)                      ≡⟨ sym (assoc _ _ _) ⟩
       (map g ∘ π₁) ∘ eqm                      ≡⟨ ∘l _ (sym (π₁-⊠ (map g))) ⟩
       (π₁ ∘ (map g ⊠)) ∘ eqm                  ≡⟨ assoc _ _ _ ⟩
       π₁ ∘ ((map g ⊠) ∘ eqm)                  ≡⟨ ∘r π₁ (sym (m-liftF (map g) (root g))) ⟩
       π₁ ∘ (eqm ∘ liftF (map g) (root g))     ≡⟨ sym (assoc _ _ _) ⟩
       (π₁ ∘ eqm) ∘ liftF (map g) (root g)     ≡⟨ ∘l _ (sym (ext-ff D′)) ⟩
       (ext D′ ∘ eqm) ∘ liftF (map g) (root g) ≡⟨ assoc _ _ _ ⟩
       ext D′ ∘ (eqm ∘ liftF (map g) (root g)) ≡⟨ ∘r _ (m-liftF _ _) ⟩
       ext D′ ∘ ((map g ⊠) ∘ eqm)              ≡⟨ sym (assoc _ _ _) ⟩
       (ext D′ ∘ (map g ⊠)) ∘ eqm ∎)

  ----------------------------------------------------------------------
  -- The terminal dialgebra

  module Final (TM : TerminalMachine) where
    open TerminalMachine TM

    -- R(T): the terminal machine restricted to the tt-part
    X : Dial
    C X = MC T
    h X = mh T
    t X = s T ∘ eqm

    η : ∀ D → DHom D X
    map  (η D) = mmap (term (J₀ D))
    root (η D) = mroot (term (J₀ D))
    step (η D) =
      ηD ∘ t D                         ≡⟨ ∘r ηD (sym (ext-tt D)) ⟩
      ηD ∘ (ext D ∘ eqm)               ≡⟨ sym (assoc _ _ _) ⟩
      (ηD ∘ ext D) ∘ eqm               ≡⟨ ∘l eqm (mstep (term (J₀ D))) ⟩
      (s T ∘ (ηD ⊠)) ∘ eqm             ≡⟨ assoc _ _ _ ⟩
      s T ∘ ((ηD ⊠) ∘ eqm)             ≡⟨ ∘r (s T) (sym (m-liftT _ _)) ⟩
      s T ∘ (eqm ∘ liftT ηD _)         ≡⟨ sym (assoc _ _ _) ⟩
      (s T ∘ eqm) ∘ liftT ηD _ ∎
      where ηD = mmap (term (J₀ D))

    natural : ∀ {Z Z′} (g : DHom Z Z′) → map (η Z′) ∘ map g ≡ map (η Z)
    natural {Z} {Z′} g = uni (J₀ Z) (mcomp (term (J₀ Z′)) (J₀-hom g))

    ηX : Hom (C X) (C X)
    ηX = map (η X)

    idem : ∀ Z → ηX ∘ map (η Z) ≡ map (η Z)
    idem Z = natural (η Z)

    -- the equaliser of id and η_X, as a dialgebra
    e : Hom (Eq id ηX) (C X)
    e = eqm

    ηXe : ηX ∘ e ≡ e
    ηXe = trans (sym eqm-eq) (idl e)

    hE : Hom (Eq id ηX) A
    hE = h X ∘ e

    le : Hom (Dom hE) (Dom (h X))
    le = liftT e refl

    tE : Hom (Dom hE) (Eq id ηX)
    tE = fact (t X ∘ le)
           (id ∘ (t X ∘ le)                       ≡⟨ idl _ ⟩
            t X ∘ le                              ≡⟨ ∘r (t X) (lift-eq e (ηX ∘ e) refl
                                                     (trans (sym (assoc _ _ _)) (∘l e (root (η X))))
                                                     (sym ηXe)) ⟩
            t X ∘ liftT (ηX ∘ e) _                ≡⟨ ∘r (t X) (sym (lift-∘ ηX e (root (η X)) refl _)) ⟩
            t X ∘ (liftT ηX (root (η X)) ∘ le)    ≡⟨ sym (assoc _ _ _) ⟩
            (t X ∘ liftT ηX (root (η X))) ∘ le    ≡⟨ ∘l le (sym (step (η X))) ⟩
            (ηX ∘ t X) ∘ le                       ≡⟨ assoc _ _ _ ⟩
            ηX ∘ (t X ∘ le) ∎)

    Tdial : Dial
    C Tdial = Eq id ηX
    h Tdial = hE
    t Tdial = tE

    eD : DHom Tdial X
    map  eD = e
    root eD = refl
    step eD = fact-β _ _

    terminal : ∀ Z → DHom Z Tdial
    map  (terminal Z) = fact (map (η Z)) (trans (idl _) (sym (idem Z)))
    root (terminal Z) =
      trans (assoc _ _ _) (trans (∘r (h X) (fact-β _ _)) (root (η Z)))
    step (terminal Z) =
      eqm-mono _ _
        (e ∘ (fZ ∘ t Z)                         ≡⟨ sym (assoc _ _ _) ⟩
         (e ∘ fZ) ∘ t Z                         ≡⟨ ∘l (t Z) (fact-β _ _) ⟩
         map (η Z) ∘ t Z                        ≡⟨ step (η Z) ⟩
         t X ∘ liftT (map (η Z)) (root (η Z))   ≡⟨ ∘r (t X) (lift-eq _ _ (root (η Z)) q (sym (fact-β _ _))) ⟩
         t X ∘ liftT (e ∘ fZ) q                 ≡⟨ ∘r (t X) (sym (lift-∘ e fZ refl rZ q)) ⟩
         t X ∘ (le ∘ liftT fZ rZ)               ≡⟨ sym (assoc _ _ _) ⟩
         (t X ∘ le) ∘ liftT fZ rZ               ≡⟨ ∘l _ (sym (fact-β _ _)) ⟩
         (e ∘ tE) ∘ liftT fZ rZ                 ≡⟨ assoc _ _ _ ⟩
         e ∘ (tE ∘ liftT fZ rZ) ∎)
      where
        fZ = fact {f = id} {ηX} (map (η Z)) (trans (idl _) (sym (idem Z)))
        rZ : hE ∘ fZ ≡ h Z
        rZ = trans (assoc _ _ _) (trans (∘r (h X) (fact-β _ _)) (root (η Z)))
        q : h X ∘ (e ∘ fZ) ≡ h Z
        q = trans (∘r (h X) (fact-β _ _)) (root (η Z))

    unique : ∀ Z (f : DHom Z Tdial) → map f ≡ map (terminal Z)
    unique Z f =
      eqm-mono _ _
        (e ∘ map f                ≡⟨ sym ηXef ⟩
         ηX ∘ (e ∘ map f)         ≡⟨ natural (dcomp eD f) ⟩
         map (η Z)                ≡⟨ sym (fact-β _ _) ⟩
         e ∘ map (terminal Z) ∎)
      where
        ηXef : ηX ∘ (e ∘ map f) ≡ e ∘ map f
        ηXef = trans (sym (assoc _ _ _)) (∘l (map f) ηXe)
