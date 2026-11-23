------------------------------------------------------------------------
-- Ledger F10f, part 4 (notes/universe-free-principles.md §3.3, G₁).
--
-- G₁, 1-truncated: the collage of a functor F : A → B of small
-- 1-categories (CocartLemmas.Cat, hom-sets with K, classical
-- unique-factorisation cocartesian arrows)
-- is a cocartesian fibration over the walking arrow I = {o0 < o1},
-- with fibre A over o0, fibre B over o1, and transport F.
--
-- The collage `Coll` is given by its hom-sets:
--   Hom (inA a) (inA a') = A.Hom a a'
--   Hom (inB b) (inB b') = B.Hom b b'
--   Hom (inA a) (inB b)  = B.Hom (F a) b        (heteromorphisms)
--   Hom (inB b) (inA a)  = ⊥
-- These are the homs that §3.3 steps 1–4 compute for the pushout
-- (A ⊗ I) ⊔_{A ⊗ {1}} B from DESC-or and DJ (steps 1–3 for the homs
-- out of inA, step 4's analogue for those out of inB).
--
-- What is machine-checked:
--   * Coll is a category and P : Coll → I is a functor;
--   * P is an opfibration in the sense of CocartLemmas (`opfib`), with
--     lifts on the nose: identities (`id-cocart`) and, over o0 → o1,
--     the heteromorphism id_{F a} : inA a → inB (F a) (`χ₁-cocart`);
--   * the fibres: the homs and composition of Coll between objects
--     over o0 are those of A, and over o1 those of B (`fibre-A-hom`,
--     `fibre-A-∘`, `fibre-B-hom`, `fibre-B-∘`; by refl, i.e. true by
--     definition of the collage);
--   * transport: the cocartesian lift of o0 → o1 at a ends at
--     inB (F a) (`transport-ob`), and the map it induces between lifts
--     at a and a' along u : a → a' is F u (`transport-hom`, stated
--     through the lift chosen by `opfib`; it is the unique such arrow
--     by IsCocart.uniq).
--
-- What is NOT machine-checked: the derivation of these hom-sets from
-- the pushout via DESC-or and DJ (§3.3 steps 1–3); here the collage is
-- *defined* by its hom-sets, so this file checks the semantic content
-- of G₁ (and that the hom computation yields a cocartesian fibration
-- with the right fibres and transport), not its derivation.  Relative
-- G₁ (over a base) and G⁺ are not encoded here.
------------------------------------------------------------------------
module CaTTExp.Descent.Collage where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas

------------------------------------------------------------------------
-- The walking arrow.

data IOb : Set where
  o0 o1 : IOb

IHom : IOb → IOb → Set
IHom o0 _  = ⊤
IHom o1 o0 = ⊥
IHom o1 o1 = ⊤

private
  Iid : ∀ {x} → IHom x x
  Iid {o0} = tt
  Iid {o1} = tt

  I∘ : ∀ {x y z} → IHom y z → IHom x y → IHom x z
  I∘ {o0} {_}  {o0} _ _ = tt
  I∘ {o0} {_}  {o1} _ _ = tt
  I∘ {o1} {o1} {o1} _ _ = tt
  I∘ {o1} {o0} {_}  _ ()
  I∘ {o1} {o1} {o0} () _

  Iprop : ∀ {x y} (f g : IHom x y) → f ≡ g
  Iprop {o0} {o0} tt tt = refl
  Iprop {o0} {o1} tt tt = refl
  Iprop {o1} {o1} tt tt = refl

I : Cat
I = record
  { Ob = IOb ; Hom = IHom ; id = Iid ; _∘_ = I∘
  ; idl = λ f → Iprop _ _ ; idr = λ f → Iprop _ _ ; assoc = λ h g f → Iprop _ _ }

------------------------------------------------------------------------
-- The collage of a functor.

module _ (A B : Cat) (F : Functor A B) where
  private
    module A = Cat A
    module B = Cat B
    open Functor F

  data CObj : Set where
    inA : A.Ob → CObj
    inB : B.Ob → CObj

  CHom : CObj → CObj → Set
  CHom (inA a) (inA a') = A.Hom a a'
  CHom (inB b) (inB b') = B.Hom b b'
  CHom (inA a) (inB b)  = B.Hom (F₀ a) b
  CHom (inB b) (inA a)  = ⊥

  private
    Cid : ∀ {x} → CHom x x
    Cid {inA a} = A.id
    Cid {inB b} = B.id

    C∘ : ∀ {x y z} → CHom y z → CHom x y → CHom x z
    C∘ {inA _} {inA _} {inA _} g f = g A.∘ f
    C∘ {inA _} {inA _} {inB _} g f = g B.∘ F₁ f
    C∘ {inA _} {inB _} {inB _} g f = g B.∘ f
    C∘ {inB _} {inB _} {inB _} g f = g B.∘ f
    C∘ {inA _} {inB _} {inA _} () f
    C∘ {inB _} {inA _} {_}     g ()
    C∘ {inB _} {inB _} {inA _} () f

    B∘-congʳ : ∀ {x y z} (g : B.Hom y z) {f f' : B.Hom x y} → f ≡ f' → g B.∘ f ≡ g B.∘ f'
    B∘-congʳ g refl = refl
    B∘-congˡ : ∀ {x y z} {g g' : B.Hom y z} (f : B.Hom x y) → g ≡ g' → g B.∘ f ≡ g' B.∘ f
    B∘-congˡ f refl = refl

    Cidl : ∀ {x y} (f : CHom x y) → C∘ {x} {y} {y} (Cid {y}) f ≡ f
    Cidl {inA _} {inA _} f = A.idl f
    Cidl {inA _} {inB _} f = B.idl f
    Cidl {inB _} {inB _} f = B.idl f

    Cidr : ∀ {x y} (f : CHom x y) → C∘ {x} {x} {y} f (Cid {x}) ≡ f
    Cidr {inA _} {inA _} f = A.idr f
    Cidr {inA _} {inB _} f = trans (B∘-congʳ f F-id) (B.idr f)
    Cidr {inB _} {inB _} f = B.idr f

    Cassoc : ∀ {w x y z} (h : CHom y z) (g : CHom x y) (f : CHom w x)
           → C∘ {w} {x} {z} (C∘ {x} {y} {z} h g) f ≡ C∘ {w} {y} {z} h (C∘ {w} {x} {y} g f)
    Cassoc {inA _} {inA _} {inA _} {inA _} h g f = A.assoc h g f
    Cassoc {inA _} {inA _} {inA _} {inB _} h g f =
      trans (B.assoc h (F₁ g) (F₁ f)) (sym (B∘-congʳ h (F-∘ g f)))
    Cassoc {inA _} {inA _} {inB _} {inB _} h g f = B.assoc h g (F₁ f)
    Cassoc {inA _} {inB _} {inB _} {inB _} h g f = B.assoc h g f
    Cassoc {inB _} {inB _} {inB _} {inB _} h g f = B.assoc h g f
    Cassoc {inA _} {inA _} {inB _} {inA _} () g f
    Cassoc {inA _} {inB _} {inA _} {_}     h () f
    Cassoc {inA _} {inB _} {inB _} {inA _} () g f
    Cassoc {inB _} {inA _} {_}     {_}     h g ()
    Cassoc {inB _} {inB _} {inA _} {_}     h () f
    Cassoc {inB _} {inB _} {inB _} {inA _} () g f

  Coll : Cat
  Coll = record
    { Ob = CObj ; Hom = CHom ; id = λ {x} → Cid {x}
    ; _∘_ = λ {x} {y} {z} g f → C∘ {x} {y} {z} g f
    ; idl = λ {x} {y} f → Cidl {x} {y} f ; idr = λ {x} {y} f → Cidr {x} {y} f
    ; assoc = λ {w} {x} {y} {z} h g f → Cassoc {w} {x} {y} {z} h g f }

  -- The projection to the walking arrow.
  private
    P₀ : CObj → IOb
    P₀ (inA _) = o0
    P₀ (inB _) = o1

    P₁ : ∀ {x y} → CHom x y → IHom (P₀ x) (P₀ y)
    P₁ {inA _} {inA _} _ = tt
    P₁ {inA _} {inB _} _ = tt
    P₁ {inB _} {inB _} _ = tt
    P₁ {inB _} {inA _} ()

  P : Functor Coll I
  P = record { F₀ = P₀ ; F₁ = P₁ ; F-id = Iprop _ _ ; F-∘ = λ _ _ → Iprop _ _ }

  module O = Over Coll I P
  open O using (IsCocart; Opfib; HasLift)

  -- Identities are cocartesian.
  id-cocart : ∀ {e} → IsCocart {e} {e} (Cid {e})
  id-cocart {e} = record
    { fact   = λ τ γ p → τ
    ; fact-P = λ τ γ p → Iprop _ _
    ; fact-∘ = λ {x} τ γ p → Cidr {e} {x} τ
    ; uniq   = λ {x} g g' q r → trans (sym (Cidr {e} {x} g)) (trans r (Cidr {e} {x} g')) }

  -- The lift of o0 → o1 at a: the identity of F a, read as a
  -- heteromorphism inA a → inB (F a).
  χ₁ : ∀ a → CHom (inA a) (inB (F₀ a))
  χ₁ a = B.id {F₀ a}

  χ₁-cocart : ∀ a → IsCocart {inA a} {inB (F₀ a)} (χ₁ a)
  χ₁-cocart a = record
    { fact   = fa
    ; fact-P = λ τ γ p → Iprop _ _
    ; fact-∘ = fa-∘
    ; uniq   = un }
    where
    fa : ∀ {x} (τ : CHom (inA a) x) (γ : IHom o1 (P₀ x)) → P₁ {inA a} {x} τ ≡ I∘ {o0} {o1} {P₀ x} γ tt
       → CHom (inB (F₀ a)) x
    fa {inB _} τ γ p = τ
    fa {inA _} τ () p
    fa-∘ : ∀ {x} (τ : CHom (inA a) x) (γ : IHom o1 (P₀ x)) (p : P₁ {inA a} {x} τ ≡ I∘ {o0} {o1} {P₀ x} γ tt)
         → C∘ {inA a} {inB (F₀ a)} {x} (fa τ γ p) (χ₁ a) ≡ τ
    fa-∘ {inB _} τ γ p = B.idr τ
    fa-∘ {inA _} τ () p
    un : ∀ {x} (g g' : CHom (inB (F₀ a)) x) → P₁ {inB (F₀ a)} {x} g ≡ P₁ {inB (F₀ a)} {x} g'
       → C∘ {inA a} {inB (F₀ a)} {x} g (χ₁ a) ≡ C∘ {inA a} {inB (F₀ a)} {x} g' (χ₁ a) → g ≡ g'
    un {inB _} g g' _ r = trans (sym (B.idr g)) (trans r (B.idr g'))
    un {inA _} () g' _ r

  -- P is an opfibration (lifts on the nose: θ = id).
  private
    iso-tt : ∀ x → Cat.IsIso I (Iid {x})
    iso-tt x = record { inv = Iid ; left = Iprop {x} {x} _ _ ; right = Iprop {x} {x} _ _ }

  opfib : Opfib
  opfib (inA a) {o0} f = record
    { tgt = inA a ; χ = Cid {inA a} ; cocart = id-cocart {inA a}
    ; θ = tt ; θ-iso = iso-tt o0 ; tri = Iprop {o0} {o0} _ _ }
  opfib (inA a) {o1} f = record
    { tgt = inB (F₀ a) ; χ = χ₁ a ; cocart = χ₁-cocart a
    ; θ = tt ; θ-iso = iso-tt o1 ; tri = Iprop {o0} {o1} _ _ }
  opfib (inB b) {o1} f = record
    { tgt = inB b ; χ = Cid {inB b} ; cocart = id-cocart {inB b}
    ; θ = tt ; θ-iso = iso-tt o1 ; tri = Iprop {o1} {o1} _ _ }
  opfib (inB b) {o0} ()

  -- Transport on objects: the lift of o0 → o1 at a ends at F a.
  transport-ob : ∀ a → HasLift.tgt (opfib (inA a) {o1} tt) ≡ inB (F₀ a)
  transport-ob a = refl

  -- Transport on arrows: for u : a → a', the unique arrow between the
  -- lifts at a and a' over id_{o1} that commutes with them is F u.
  transport-hom : ∀ {a a'} (u : A.Hom a a')
    → IsCocart.fact (HasLift.cocart (opfib (inA a) {o1} tt)) {inB (F₀ a')}
        (C∘ {inA a} {inA a'} {inB (F₀ a')} (χ₁ a') u) tt (Iprop {o0} {o1} _ _)
      ≡ F₁ u
  transport-hom {a} {a'} u = B.idl (F₁ u)

  -- The fibres (true by definition of the collage).
  fibre-A-hom : ∀ a a' → CHom (inA a) (inA a') ≡ A.Hom a a'
  fibre-A-hom a a' = refl

  fibre-A-∘ : ∀ {a a' a''} (g : A.Hom a' a'') (f : A.Hom a a')
            → Cat._∘_ Coll {inA a} {inA a'} {inA a''} g f ≡ g A.∘ f
  fibre-A-∘ g f = refl

  fibre-B-hom : ∀ b b' → CHom (inB b) (inB b') ≡ B.Hom b b'
  fibre-B-hom b b' = refl

  fibre-B-∘ : ∀ {b b' b''} (g : B.Hom b' b'') (f : B.Hom b b')
            → Cat._∘_ Coll {inB b} {inB b'} {inB b''} g f ≡ g B.∘ f
  fibre-B-∘ g f = refl

  -- Nothing over o1 maps back to o0.
  no-backward : ∀ b a → CHom (inB b) (inA a) ≡ ⊥
  no-backward b a = refl
