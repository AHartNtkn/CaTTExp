------------------------------------------------------------------------
-- Ledger F10f, part 3: EX (notes/universe-free-principles.md §3.3) and
-- encode–decode for graphs (§6a), 1-truncated shadows.
--
-- Part A, EX from propositional descent.  §3.3 derives effectiveness
-- of quotients in three steps: (1) DESC-grpd glues the family
-- R(x, –) to a family over X × C; (2) DESC-tr pushes a family of
-- propositions down to X × Q; (3) encode–decode: transport along
-- q x ≅ q y carries refl to a point of R(x, y).  The output of steps
-- 1–2 is taken as the hypothesis `PropDescent` (R-compatible families
-- of propositions on X descend along q), and step 3 is checked (`ex`).
-- The hypothesis does all the work: given R-transport, PropDescent is
-- equivalent to EX itself (`descent-from-ex`), so `ex` checks only that
-- step 3 is a correct reduction (transport of refl along q x ≡ q y),
-- not that EX is hard.  The hypothesis is satisfiable (`ex-model`, the
-- identity quotient) and not automatic: a map q that merely respects R
-- need not satisfy it (`ex-needs-descent`: q : Bool → ⊤ respects
-- equality, but EX and hence PropDescent fail).  q here is any map
-- respecting R; the quotient ‖coeq(r₀, r₁)‖₀ is not constructed.
--
-- Part B, encode–decode for graphs (§6a steps 3–6), with
-- Hom_{⟦Γ⟧}(a, –) *defined* as the inductive type `Path` of paths from
-- a.  No free category is constructed (no composition, laws or
-- universal property).  `Path` is itself an initial model
-- (`paths-initial`), so `hom≅Π` is uniqueness of initial models up to
-- iso, organised as §6a's encode–decode:
--   * encode (role of §6a step 3): enc is the fold of Π along paths
--     (Path's recursor), standing in for DJ-sec applied to G's
--     transport; no covering family is built;
--   * decode (step 4): the model morphism Π → Path given by Π's
--     initiality (stated pointwise, no function extensionality);
--   * dec ∘ enc = id (step 5): by path induction, i.e. uniqueness of
--     maps out of the initial model `Path` (INIT-J2 for Path).  This is
--     the instance of DJ-uni's conclusion for the free category, but it
--     is not proved from DJ;
--   * enc ∘ dec = id (step 6, INIT-J2 for Π): enc is a model morphism,
--     so enc ∘ dec is an endomorphism of Π, hence the identity.
--
-- What is NOT machine-checked:
--   * DESC-grpd and DESC-tr themselves (Part A takes their output as a
--     hypothesis); the coequaliser C, the set truncation Q = ‖C‖₀ and
--     the exponential law of step 1;
--   * DJ: step 5 is path induction (initiality of `Path`), not DJ;
--     `CaTTExp.Descent.DJOneTruncated` is not used;
--   * the free category ⟦Γ⟧ and its universal property (R-A):
--     Hom_{⟦Γ⟧}(a, –) is defined as `Path`;
--   * the covering family over ⟦Γ⟧ glued from collages (G), step 4's
--     assembly of the fibrewise decode maps into a CF-morphism
--     (DESC-uni), and step 1's reduction of many sorts to one sort over
--     V;
--   * DESC and INIT as declared operations over an abstract model
--     interface (initiality is a hypothesis record here);
--   * localisation (T-loc, inverted edges with bi-invertibility data),
--     and homs over generalised points (the slice version §6a needs to
--     reach T-graph's statement; that step is T-hom⁻, part 6);
--   * truncation levels: in this encoding every Agda Set is a set (K),
--     so "Hom(a, b) trunc 0" is automatic; the content checked is the
--     identification Path ≅ Π_b, not its truncation level.
------------------------------------------------------------------------
module CaTTExp.Descent.EncodeDecode where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Part A: EX from propositional descent.

IsProp : Set → Set
IsProp S = (s t : S) → s ≡ t

module EX (X : Set) (R : X → X → Set)
          (R-prop : ∀ x y → IsProp (R x y))
          (R-refl : ∀ x → R x x)
          (R-sym : ∀ {x y} → R x y → R y x)
          (R-trans : ∀ {x y z} → R x y → R y z → R x z)
          (Q : Set) (q : X → Q) (q-resp : ∀ {x y} → R x y → q x ≡ q y) where

  -- The output of §3.3 steps 1–2: R-compatible families of
  -- propositions on X descend along q.
  PropDescent : Set₁
  PropDescent = ∀ (P : X → Set) → (∀ x → IsProp (P x))
              → (∀ {x y} → R x y → P x → P y)
              → Σ (Q → Set) (λ P' → ∀ x → (P' (q x) → P x) × (P x → P' (q x)))

  -- Step 3, encode–decode: effectiveness.
  ex : PropDescent → ∀ {x y} → q x ≡ q y → R x y
  ex desc {x} {y} e = fst (snd D y) (subst P' e (snd (snd D x) (R-refl x)))
    where
    D = desc (R x) (R-prop x) (λ r p → R-trans p r)
    P' = fst D

  -- Conversely, EX gives PropDescent (no prop or symmetry needed), so
  -- the hypothesis is equivalent to the conclusion.
  descent-from-ex : (∀ {x y} → q x ≡ q y → R x y) → PropDescent
  descent-from-ex ex' P _ comp =
    (λ c → Σ X (λ x' → Σ (q x' ≡ c) (λ _ → P x'))) ,
    λ x → (λ { (x' , e , p) → comp (ex' e) p }) , (λ p → x , refl , p)

  -- The converse inclusion R ⊆ X ×_Q X is q-resp; so R ≅ X ×_Q X as
  -- subobjects of X × X.
  ex-iff : PropDescent → ∀ {x y} → (q x ≡ q y → R x y) × (R x y → q x ≡ q y)
  ex-iff desc = ex desc , q-resp

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

-- Satisfiable: the discrete quotient of the equality relation.
ex-model : ∀ (X : Set)
         → EX.PropDescent X _≡_ (λ _ _ → uip) (λ _ → refl) sym trans X (λ x → x) (λ e → e)
ex-model X P _ _ = P , λ x → (λ p → p) , (λ p → p)

-- Not automatic: q : Bool → ⊤ respects equality, but EX, hence
-- PropDescent, fails.
ex-needs-descent :
  let module E = EX Bool _≡_ (λ _ _ → uip) (λ _ → refl) sym trans ⊤ (λ _ → tt) (λ _ → refl)
  in (E.PropDescent → ⊥) × ((∀ {x y : Bool} → tt ≡ tt → x ≡ y) → ⊥)
ex-needs-descent = (λ d → true≢false (E.ex d {true} {false} refl)) , (λ f → true≢false (f refl))
  where
  module E = EX Bool _≡_ (λ _ _ → uip) (λ _ → refl) sym trans ⊤ (λ _ → tt) (λ _ → refl)

------------------------------------------------------------------------
-- Part B: encode–decode for the free category of a graph.

module Graph (V : Set) (Ed : V → V → Set) (a : V) where

  -- Hom_{⟦Γ⟧}(a, –): paths from a (snoc lists of edges).
  data Path : V → Set where
    nil  : Path a
    snoc : ∀ {v w} → Path v → Ed v w → Path w

  -- Models of the context (X_v, nil : ⊤ → X_a, snoc_e : X_v → X_w).
  record Model : Set₁ where
    field
      M  : V → Set
      m  : M a
      sn : ∀ {v w} → Ed v w → M v → M w

  record Mor (A B : Model) : Set where
    private
      module A = Model A
      module B = Model B
    field
      f      : ∀ v → A.M v → B.M v
      f-nil  : f a A.m ≡ B.m
      f-snoc : ∀ {v w} (e : Ed v w) (x : A.M v) → f w (A.sn e x) ≡ B.sn e (f v x)

  idMor : ∀ A → Mor A A
  idMor A = record { f = λ _ x → x ; f-nil = refl ; f-snoc = λ _ _ → refl }

  _∘M_ : ∀ {A B C} → Mor B C → Mor A B → Mor A C
  _∘M_ {A} {B} {C} g h = record
    { f      = λ v x → G.f v (H.f v x)
    ; f-nil  = trans (cong (G.f a) H.f-nil) G.f-nil
    ; f-snoc = λ e x → trans (cong (G.f _) (H.f-snoc e x)) (G.f-snoc e (H.f _ x)) }
    where
    module G = Mor g
    module H = Mor h

  -- Initiality, pointwise.
  record Initial (Π : Model) : Set₁ where
    field
      init : ∀ B → Mor Π B
      uniq : ∀ B (g h : Mor Π B) → ∀ v x → Mor.f g v x ≡ Mor.f h v x

  PathModel : Model
  PathModel = record { M = Path ; m = nil ; sn = λ e p → snoc p e }

  module _ (Π : Model) (ini : Initial Π) where
    private
      module Π = Model Π
      module I = Initial ini

    -- Steps 2–3: transport of nil along a path (G's transport for the
    -- family Π over ⟦Γ⟧), i.e. encode.
    enc : ∀ v → Path v → Π.M v
    enc .a nil        = Π.m
    enc w  (snoc p e) = Π.sn e (enc _ p)

    encMor : Mor PathModel Π
    encMor = record { f = enc ; f-nil = refl ; f-snoc = λ e p → refl }

    -- Step 4: decode by initiality.
    decMor : Mor Π PathModel
    decMor = I.init PathModel

    private
      dec = Mor.f decMor
      module D = Mor decMor

    -- Step 5: dec ∘ enc = id, by path induction (DJ for ⟦Γ⟧).
    dec-enc : ∀ v (p : Path v) → dec v (enc v p) ≡ p
    dec-enc .a nil        = D.f-nil
    dec-enc w  (snoc p e) = trans (D.f-snoc e (enc _ p)) (cong (λ r → snoc r e) (dec-enc _ p))

    -- Step 6: enc ∘ dec = id, by uniqueness (INIT-J2).
    enc-dec : ∀ v (x : Π.M v) → enc v (dec v x) ≡ x
    enc-dec v x = I.uniq Π (encMor ∘M decMor) (idMor Π) v x

    hom≅Π : ∀ v → Σ (Path v → Π.M v) (λ en → Σ (Π.M v → Path v) (λ de →
              (∀ p → de (en p) ≡ p) × (∀ x → en (de x) ≡ x)))
    hom≅Π v = enc v , dec v , dec-enc v , enc-dec v

  -- Satisfiable: paths are an initial model.
  paths-initial : Initial PathModel
  paths-initial = record { init = fold ; uniq = un }
    where
    fold : ∀ B → Mor PathModel B
    fold B = record { f = go ; f-nil = refl ; f-snoc = λ e p → refl }
      where
      module B = Model B
      go : ∀ v → Path v → B.M v
      go .a nil        = B.m
      go w  (snoc p e) = B.sn e (go _ p)
    un : ∀ B (g h : Mor PathModel B) → ∀ v x → Mor.f g v x ≡ Mor.f h v x
    un B g h .a nil        = trans (Mor.f-nil g) (sym (Mor.f-nil h))
    un B g h w  (snoc p e) =
      trans (Mor.f-snoc g e p) (trans (cong (Model.sn B e) (un B g h _ p)) (sym (Mor.f-snoc h e p)))
