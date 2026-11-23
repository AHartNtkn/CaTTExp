------------------------------------------------------------------------
-- Ledger F10i (notes/descent-vs-init.md §3).
--
-- DESC is not derivable from INIT.  Two locally discrete models of the
-- non-DESC rules in which INIT holds and a DESC clause fails.  This
-- file machine-checks the 1-categorical (in fact 0-truncated) shadow
-- of the parts that decide the question.
--
-- Part I.  The model Set with discrete homs (every ambient cell of
-- dimension ≥ 2 an identity; internal cells of every object are
-- identities).  Agda's Set with K (this library is --safe, K on) is
-- that model's underlying 1-category.  Equality of maps is rendered
-- pointwise throughout (no function extensionality under --safe).
--   (I.1) `S¹-initial`: the one-point set with b = tt, l = refl is the
--         initial model of Δ_S¹ = (X, b : ⊤ → X, l : b → b, l inv):
--         existence of a strong model morphism to every model (J1) and
--         uniqueness of model morphisms (J2): the maps agree pointwise
--         and the b-cells agree (`S¹-uni-cell`); the l-cells then agree
--         by UIP.  The inv mark on l needs no certificate: every ≡ is
--         invertible.
--   (I.2) `ℤ-initial`: the integers with z = 0 and s = suc, whose
--         `inv` mark is certified by bi-invertibility data, form the
--         initial model of Δ_ℤ = (X, z : ⊤ → X, s : X → X inv):
--         recursion, its computation equations, and pointwise
--         uniqueness of the map (agreement of the z- and s-cells is
--         then immediate by UIP, not stated).
--   (I.3) `ΩS¹-prop` and `ΩS¹≄ℤ`: Hom_{S¹}(b, b), which in this model
--         is b ≡ b, is a proposition, while ℤ is not; so ΩS¹ ≃ ℤ fails.
--   (I.4) `no-glue`: DESC-glue fails.  Descent data over the
--         coequaliser Q of id, id : ⊤ ⇉ ⊤ (whose colimit in Set is ⊤,
--         equal to S¹ above) are a set F with an automorphism φ.  A
--         gluing is a family over Q whose fibre is identified with F
--         so that transport along the coequalising cell κ is φ.  Here
--         κ ≡ refl (UIP), so transport is the identity and any gluing
--         forces φ = id.  A gluing is only assumed to give a split
--         surjection from the fibre onto F (not an equivalence), which
--         makes the negative result stronger.  `no-glue-ℤ`: (ℤ, suc) has no gluing.
--
-- Part II.  The model 2 = {false < true} (a complete Heyting algebra
-- viewed as a thin, locally discrete ω-category).  ⊤ = true, ∅ =
-- false, coproduct = ∨, pullback = ∧, every hom a subsingleton.
--   (II.1) every operator f : Bool → Bool has a least prefixed point,
--          namely f false (only the monotone case is used).  In a thin
--          model the models of a single-sorted positive context are the
--          prefixed points of the join of its operations' sources, so
--          `lfp-pre` is INIT-form (μ is a model), `lfp-least` is J1, and
--          `≤-prop` (homs are subsingletons) is J2.
--   (II.2) `pb-univ`, `coprod-univ`: ∧ and ∨ are the pullback and the
--          coproduct.  `distrib`: binary coproducts are universal (the
--          nullary and other cases are trivial in a thin model, not
--          stated).
--   (II.3) `not-disjoint`: ⊤ ×_{⊤ ⊔ ⊤} ⊤ = true is not ∅, so the two
--          coproduct injections are not disjoint (T-coprod fails), and
--          `no-glue-coprod`: DESC-grpd's gluing of (⊤ over the first
--          summand, ∅ over the second) has no solution.
--
-- Scope and honesty notes.
--   * NOT encoded: that these models satisfy every non-DESC rule of
--     chapters 1–9 (argued in notes/descent-vs-init.md §3 on the
--     pattern of the verified Pos model, conjectures/answered/
--     non-derivability-2026-11-18.md §1); that INIT holds for every
--     positive context in Set (Adámek–Rosický, argued in the note);
--     that the cell structure is discrete above dimension 1 and that
--     Hom_X(x, y) is x ≡ y (both are the model's definition, not
--     theorems); that ⊤ with κ is the coequaliser of id, id : ⊤ ⇉ ⊤ in
--     Set and coincides with the INIT object S¹ (both are ⊤ here, no
--     universal property or iso is stated); that Set satisfies DESC-univ
--     and EX (used in the note's reading of Model A); the reduction of
--     a thin positive context to one operator (II.1); the note's
--     Hom_{⟦L⟧}(x, x) ≄ ℕ instance and Model C (Pos), which are argued
--     in the note or checked in `PushoutNotUniversal`.
--   * (I.2) encodes Δ_ℤ's model notion in the Set model: a set with a
--     point and a bijection; morphisms commute with z and s (the
--     inverse is then preserved automatically, not stated).
--   * (II.1) encodes INIT for thin models only through the
--     single-operator reduction; Hom-targets (which in 2 need X = true)
--     and several sorts are not encoded.
------------------------------------------------------------------------
module CaTTExp.Descent.InitNotDesc where

open import CaTTExp.Prelude

-- Uniqueness of identity proofs (K is on in this library).
uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

------------------------------------------------------------------------
-- Part I.  Set with discrete homs.

-- (I.1)  The circle context.

record S¹-Model : Set₁ where
  field
    Car : Set
    b   : Car
    l   : b ≡ b
open S¹-Model

-- A strong model morphism: a map, an invertible cell on b, and the
-- l-cell (f ∘ l, conjugated by the b-cell, is l').
record S¹-Mor (M N : S¹-Model) : Set where
  field
    map  : Car M → Car N
    on-b : map (b M) ≡ b N
    on-l : trans (sym on-b) (trans (cong map (l M)) on-b) ≡ l N
open S¹-Mor

S¹ : S¹-Model
S¹ = record { Car = ⊤ ; b = tt ; l = refl }

-- J1: a model morphism to every model.
S¹-rec : (N : S¹-Model) → S¹-Mor S¹ N
S¹-rec N = record { map = λ _ → b N ; on-b = refl ; on-l = uip _ _ }

-- J2: any two model morphisms out of S¹ agree pointwise, and their
-- b-cells agree (the l-cells then agree by UIP).
S¹-uni : ∀ {N} (h h' : S¹-Mor S¹ N) →
         (∀ x → map h x ≡ map h' x)
S¹-uni h h' tt = trans (on-b h) (sym (on-b h'))

S¹-uni-cell : ∀ {N} (h h' : S¹-Mor S¹ N) →
              on-b h ≡ trans (S¹-uni h h' tt) (on-b h')
S¹-uni-cell h h' = uip _ _

S¹-initial : (∀ N → S¹-Mor S¹ N) × (∀ {N} (h h' : S¹-Mor S¹ N) → ∀ x → map h x ≡ map h' x)
S¹-initial = S¹-rec , S¹-uni

-- (I.3, first half)  Hom_{S¹}(b, b) is the identity type b ≡ b, a
-- proposition.
ΩS¹ : Set
ΩS¹ = b S¹ ≡ b S¹

ΩS¹-prop : (p q : ΩS¹) → p ≡ q
ΩS¹-prop = uip

-- (I.2)  The integers and the context (X, z, s inv).

data ℤ : Set where
  pos    : Nat → ℤ
  negsuc : Nat → ℤ

sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

suc-pred : ∀ i → sucℤ (predℤ i) ≡ i
suc-pred (pos zero)    = refl
suc-pred (pos (suc n)) = refl
suc-pred (negsuc n)    = refl

pred-suc : ∀ i → predℤ (sucℤ i) ≡ i
pred-suc (pos n)          = refl
pred-suc (negsuc zero)    = refl
pred-suc (negsuc (suc n)) = refl

-- A model of Δ_ℤ in Set: the inv mark on s is certified by an inverse
-- with both laws (bi-invertibility data; in Set a two-sided inverse).
record ℤ-Model : Set₁ where
  field
    Car  : Set
    z    : Car
    s    : Car → Car
    s⁻   : Car → Car
    s-s⁻ : ∀ x → s (s⁻ x) ≡ x
    s⁻-s : ∀ x → s⁻ (s x) ≡ x
open ℤ-Model

record ℤ-Mor (M N : ℤ-Model) : Set where
  field
    fun  : Car M → Car N
    on-z : fun (z M) ≡ z N
    on-s : ∀ x → fun (s M x) ≡ s N (fun x)
open ℤ-Mor

ℤM : ℤ-Model
ℤM = record { Car = ℤ ; z = pos zero ; s = sucℤ ; s⁻ = predℤ
            ; s-s⁻ = suc-pred ; s⁻-s = pred-suc }

module _ (N : ℤ-Model) where
  private
    iter : Nat → Car N
    iter zero    = z N
    iter (suc n) = s N (iter n)

    iter⁻ : Nat → Car N
    iter⁻ zero    = s⁻ N (z N)
    iter⁻ (suc n) = s⁻ N (iter⁻ n)

  recℤ : ℤ → Car N
  recℤ (pos n)    = iter n
  recℤ (negsuc n) = iter⁻ n

  recℤ-s : ∀ i → recℤ (sucℤ i) ≡ s N (recℤ i)
  recℤ-s (pos n)          = refl
  recℤ-s (negsuc zero)    = sym (s-s⁻ N (z N))
  recℤ-s (negsuc (suc n)) = sym (s-s⁻ N (iter⁻ n))

  ℤ-rec : ℤ-Mor ℤM N
  ℤ-rec = record { fun = recℤ ; on-z = refl ; on-s = recℤ-s }

  -- Uniqueness: every model morphism is pointwise equal to recℤ.
  ℤ-uni : (h : ℤ-Mor ℤM N) → ∀ i → fun h i ≡ recℤ i
  ℤ-uni h (pos zero)    = on-z h
  ℤ-uni h (pos (suc n)) = trans (on-s h (pos n)) (cong (s N) (ℤ-uni h (pos n)))
  ℤ-uni h (negsuc zero) =
    -- h(-1) = s⁻(s(h(-1))) = s⁻(h(0)) = s⁻ z
    trans (sym (s⁻-s N (fun h (negsuc zero))))
          (cong (s⁻ N) (trans (sym (on-s h (negsuc zero))) (on-z h)))
  ℤ-uni h (negsuc (suc n)) =
    trans (sym (s⁻-s N (fun h (negsuc (suc n)))))
          (cong (s⁻ N) (trans (sym (on-s h (negsuc (suc n)))) (ℤ-uni h (negsuc n))))

ℤ-initial : (∀ N → ℤ-Mor ℤM N) ×
            (∀ N (h h' : ℤ-Mor ℤM N) → ∀ i → fun h i ≡ fun h' i)
ℤ-initial = ℤ-rec , λ N h h' i → trans (ℤ-uni N h i) (sym (ℤ-uni N h' i))

-- (I.3, second half)  ΩS¹ ≃ ℤ fails: ℤ is not a proposition.
pos≢ : ¬ (pos zero ≡ pos (suc zero))
pos≢ ()

ΩS¹≄ℤ : ¬ Σ (ΩS¹ → ℤ) (λ f → Σ (ℤ → ΩS¹) (λ g → ∀ i → f (g i) ≡ i))
ΩS¹≄ℤ (f , g , fg) =
  pos≢ (trans (sym (fg (pos zero)))
              (trans (cong f (ΩS¹-prop (g (pos zero)) (g (pos (suc zero)))))
                     (fg (pos (suc zero)))))

-- (I.4)  DESC-glue fails over the coequaliser of id, id : ⊤ ⇉ ⊤.
-- The colimit is Q = ⊤ with leg ι = tt and coequalising cell κ : ι ≡ ι.
-- A family over Q is a set E with p : E → Q; its fibre over ι is
-- Fib E = Σ E (λ e → p e ≡ tt); transport along κ acts on fibres by
-- subst.  A gluing of descent data (F, φ) is an equivalence e between
-- the fibre and F under which transport along κ becomes φ.

module Glue (κ : tt ≡ tt) where
  Fib : (E : Set) (p : E → ⊤) → Set
  Fib E p = Σ E (λ e → p e ≡ tt)

  transport : ∀ {E p} → Fib E p → Fib E p
  transport (e , q) = e , trans q κ

  record Gluing (F : Set) (φ : F → F) : Set₁ where
    field
      E     : Set
      p     : E → ⊤
      e     : Fib E p → F
      e⁻    : F → Fib E p
      e-e⁻  : ∀ y → e (e⁻ y) ≡ y
      compat : ∀ w → e (transport w) ≡ φ (e w)

  -- Transport along κ is the identity (κ ≡ refl by UIP) ...
  transport-id : ∀ {E p} (w : Fib E p) → transport w ≡ w
  transport-id (e , q) = cong (λ r → e , r) (uip _ _)

  -- ... so a gluing forces φ to be the identity.
  glue⇒id : ∀ {F φ} → Gluing F φ → ∀ y → φ y ≡ y
  glue⇒id {φ = φ} G y =
    trans (cong φ (sym (e-e⁻ y)))
          (trans (sym (compat (e⁻ y)))
                 (trans (cong e (transport-id (e⁻ y))) (e-e⁻ y)))
    where open Gluing G

open Glue using (Gluing; glue⇒id)

no-glue : ∀ (κ : tt ≡ tt) {F φ} → (Σ F (λ y → ¬ (φ y ≡ y))) → ¬ Gluing κ F φ
no-glue κ (y , ne) G = ne (glue⇒id κ G y)

-- The universal-cover data (ℤ, suc) does not glue.
no-glue-ℤ : ∀ κ → ¬ Gluing κ ℤ sucℤ
no-glue-ℤ κ = no-glue κ (pos zero , λ ())

------------------------------------------------------------------------
-- Part II.  The two-element lattice.

infix 4 _≤_
data _≤_ : Bool → Bool → Set where
  f≤ : ∀ {x} → false ≤ x
  t≤t : true ≤ true

≤-prop : ∀ {x y} (p q : x ≤ y) → p ≡ q
≤-prop f≤  f≤  = refl
≤-prop t≤t t≤t = refl

≤-true : ∀ x → x ≤ true
≤-true false = f≤
≤-true true  = t≤t

-- (II.1)  Least prefixed points: lfp f = f false, for every f.
lfp : (Bool → Bool) → Bool
lfp f = f false

lfp-pre : ∀ f → f (lfp f) ≤ lfp f
lfp-pre f = go (f false) refl
  where
  go : ∀ v → f false ≡ v → f v ≤ v
  go false q = subst (λ w → w ≤ false) (sym q) f≤
  go true  _ = ≤-true (f true)

lfp-least : ∀ f x → f x ≤ x → lfp f ≤ x
lfp-least f true  _ = ≤-true (f false)
lfp-least f false p = p

-- (II.2)  ∧ is the pullback (meet), ∨ the coproduct (join).
∧-l : ∀ a b → a ∧ b ≤ a
∧-l false b     = f≤
∧-l true  false = f≤
∧-l true  true  = t≤t

∧-r : ∀ a b → a ∧ b ≤ b
∧-r false b = f≤
∧-r true  b with b
... | false = f≤
... | true  = t≤t

pb-univ : ∀ {x a b} → x ≤ a → x ≤ b → x ≤ a ∧ b
pb-univ f≤  _   = f≤
pb-univ t≤t t≤t = t≤t

∨-l : ∀ a b → a ≤ a ∨ b
∨-l false b = f≤
∨-l true  b = t≤t

∨-r : ∀ a b → b ≤ a ∨ b
∨-r false b = ≤-refl b where
  ≤-refl : ∀ x → x ≤ x
  ≤-refl false = f≤
  ≤-refl true  = t≤t
∨-r true  b = ≤-true b

coprod-univ : ∀ {a b x} → a ≤ x → b ≤ x → a ∨ b ≤ x
coprod-univ f≤  q = q
coprod-univ t≤t _ = t≤t

-- Universality of coproducts (frame distributivity) holds.
distrib : ∀ a b c → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
distrib false b c = refl
distrib true  b c = refl

-- (II.3)  Disjointness fails: ⊤ ×_{⊤⊔⊤} ⊤ = true ∧ true = true ≰ false = ∅.
not-disjoint : ¬ (true ∧ true ≤ false)
not-disjoint ()

-- DESC-grpd over the coproduct ⊤ ⊔ ⊤ = true: glue E₁ = ⊤ = true over the
-- first summand with E₂ = ∅ = false over the second.  A solution is
-- E ≤ true whose pullbacks along both legs (E ∧ true) are true and false.
no-glue-coprod : ¬ Σ Bool (λ E → (E ∧ true ≡ true) × (E ∧ true ≡ false))
no-glue-coprod (false , () , _)
no-glue-coprod (true  , _  , ())
