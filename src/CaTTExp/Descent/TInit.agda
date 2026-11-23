------------------------------------------------------------------------
-- Ledger F10f, part 6 (T-init half; notes/universe-free-principles.md
-- §6a, T-init).
--
-- T-init at n = 0, 1-truncated, for finitary signatures without cell
-- variables.  A signature is a family of operations i : Op, each with
-- a parameter category A i and an arity ar i : Nat; its polynomial
-- endofunctor of Cat is
--     P X = Σ_i A i × X^(ar i)
-- (a source built from coproducts, finite products, parameters and X
-- normalises to this form).  Initial models are taken in the
-- 2-categorical sense that the 1-truncated shadow of INIT gives:
-- algebra maps are *pseudo* (the square commutes up to a natural
-- isomorphism), and initiality says every algebra receives one, and
-- any two endomaps of the initial algebra are naturally isomorphic.
-- (Bi-initiality implies it, so assuming it is no stronger than assuming
-- bi-initiality.)
--
-- What is machine-checked (`tinit`): if every parameter A i is
-- trunc 0 (a groupoid with at most one arrow between two objects), then
-- the carrier of any initial algebra in this sense is trunc 0.
-- Proof: the category W of trees over the signature, with arrows
-- componentwise, is trunc 0 (`W-grpd`, `W-thin`) and is an algebra
-- (`β`); the evident s : W → μ is a pseudo algebra map (`sAlg`); with
-- the map h : μ → W given by initiality, s ∘ h ≅ id by uniqueness, so
-- μ is a retract up to natural isomorphism of a trunc 0 category, hence
-- trunc 0.  No function extensionality is used: equalities of functors
-- never occur, only natural isomorphisms.
-- The hypothesis is satisfiable: with trunc 0 parameters, W itself is
-- initial in this sense (`W-initial`; maps out of W by recursion,
-- uniqueness by induction on trees).
-- At n ≥ 1 T-init is vacuous in 1-categories (`tinit-≥1`).
--
-- What is NOT machine-checked:
--   * that INIT's μΔ, read in Cat, is an algebra satisfying `Initial`
--     (`tinit` takes μ and its initiality as hypotheses; W shows such
--     algebras exist for trunc 0 parameters);
--   * that `Initial` is implied by INIT's initiality (argued: INIT's
--     universal property is stated by cells; its 1-truncated shadow is
--     bi-initiality among algebras and pseudo maps, which implies
--     `Initial`; a merely strict initial algebra would need a separate
--     argument that it is also bi-initial);
--   * signatures with cell variables, in particular inv marks
--     (bi-invertibility data, as for ℤ); T-init with inv marks stays
--     argued (note §6a);
--   * the reduction of an arbitrary source (built from ⊔, ×, parameters
--     and X) to the normal form Σ_i A i × X^(ar i) (distributivity in
--     Cat), the transfer of `Initial` along that isomorphism of
--     endofunctors, and the closure of trunc 0 under the finite
--     products, including ⊤, forming A i (TruncGrpdModel has `prod`
--     and `prod′`);
--   * the content of T-init at n ≥ 1 (cells of dimension ≥ 2, which a
--     1-truncated encoding does not have; `tinit-≥1` is trivial), and
--     the ω-categorical model, of which this is the 1-truncated shadow.
------------------------------------------------------------------------
module CaTTExp.Descent.TInit where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas
open import CaTTExp.Descent.TruncGrpdModel using (Lvl; l0; l1; T0; Trunc; IsGrpd; Thin)

------------------------------------------------------------------------
-- Generic category helpers.

_∘F_ : ∀ {B C D} → Functor C D → Functor B C → Functor B D
_∘F_ {B} {C} {D} G H = record
  { F₀ = λ x → G.F₀ (H.F₀ x)
  ; F₁ = λ f → G.F₁ (H.F₁ f)
  ; F-id = trans (cong G.F₁ H.F-id) G.F-id
  ; F-∘ = λ g f → trans (cong G.F₁ (H.F-∘ g f)) (G.F-∘ (H.F₁ g) (H.F₁ f)) }
  where
  module G = Functor G
  module H = Functor H

idF : ∀ {C} → Functor C C
idF = record { F₀ = λ x → x ; F₁ = λ f → f ; F-id = refl ; F-∘ = λ _ _ → refl }

module CR (C : Cat) where
  open Cat C
  congˡ : ∀ {x y z} {g g' : Hom y z} (f : Hom x y) → g ≡ g' → g ∘ f ≡ g' ∘ f
  congˡ f refl = refl
  congʳ : ∀ {x y z} (g : Hom y z) {f f' : Hom x y} → f ≡ f' → g ∘ f ≡ g ∘ f'
  congʳ g refl = refl

  iso-∘ : ∀ {a b c} {f : Hom b c} {g : Hom a b} → IsIso f → IsIso g → IsIso (f ∘ g)
  iso-∘ {f = f} {g} i j = record
    { inv   = g⁻ ∘ f⁻
    ; left  =
        (g⁻ ∘ f⁻) ∘ (f ∘ g)     ≡⟨ assoc _ _ _ ⟩
        g⁻ ∘ (f⁻ ∘ (f ∘ g))     ≡⟨ congʳ g⁻ (sym (assoc _ _ _)) ⟩
        g⁻ ∘ ((f⁻ ∘ f) ∘ g)     ≡⟨ congʳ g⁻ (congˡ g (IsIso.left i)) ⟩
        g⁻ ∘ (id ∘ g)           ≡⟨ congʳ g⁻ (idl g) ⟩
        g⁻ ∘ g                  ≡⟨ IsIso.left j ⟩
        id ∎
    ; right =
        (f ∘ g) ∘ (g⁻ ∘ f⁻)     ≡⟨ assoc _ _ _ ⟩
        f ∘ (g ∘ (g⁻ ∘ f⁻))     ≡⟨ congʳ f (sym (assoc _ _ _)) ⟩
        f ∘ ((g ∘ g⁻) ∘ f⁻)     ≡⟨ congʳ f (congˡ f⁻ (IsIso.right j)) ⟩
        f ∘ (id ∘ f⁻)           ≡⟨ congʳ f (idl f⁻) ⟩
        f ∘ f⁻                  ≡⟨ IsIso.right i ⟩
        id ∎ }
    where
    f⁻ = IsIso.inv i
    g⁻ = IsIso.inv j

  id-iso : ∀ {x} → IsIso (id {x})
  id-iso = record { inv = id ; left = idl id ; right = idl id }

  inv-iso : ∀ {x y} {f : Hom x y} (i : IsIso f) → IsIso (IsIso.inv i)
  inv-iso {f = f} i = record { inv = f ; left = IsIso.right i ; right = IsIso.left i }

  -- f = θ' ∘ g ∘ θ⁻¹ from θ' ∘ g ≡ f ∘ θ.
  conj : ∀ {x y x' y'} {f : Hom x y} {g : Hom x' y'} {θ : Hom x' x} {θ' : Hom y' y}
       → (i : IsIso θ) → θ' ∘ g ≡ f ∘ θ → f ≡ (θ' ∘ g) ∘ IsIso.inv i
  conj {f = f} {g} {θ} {θ'} i e =
    f                              ≡⟨ sym (idr f) ⟩
    f ∘ id                         ≡⟨ congʳ f (sym (IsIso.right i)) ⟩
    f ∘ (θ ∘ IsIso.inv i)          ≡⟨ sym (assoc _ _ _) ⟩
    (f ∘ θ) ∘ IsIso.inv i          ≡⟨ congˡ _ (sym e) ⟩
    (θ' ∘ g) ∘ IsIso.inv i ∎

F-iso : ∀ {C D} (F : Functor C D) {x y} {f : Cat.Hom C x y}
      → Cat.IsIso C f → Cat.IsIso D (Functor.F₁ F f)
F-iso F {f = f} i = record
  { inv   = Functor.F₁ F (Cat.IsIso.inv i)
  ; left  = trans (sym (Functor.F-∘ F _ f)) (trans (cong (Functor.F₁ F) (Cat.IsIso.left i)) (Functor.F-id F))
  ; right = trans (sym (Functor.F-∘ F f _)) (trans (cong (Functor.F₁ F) (Cat.IsIso.right i)) (Functor.F-id F)) }

------------------------------------------------------------------------
-- Natural isomorphisms.

record NatIso {C D : Cat} (G G' : Functor C D) : Set where
  private
    module C = Cat C
    module D = Cat D
    module G = Functor G
    module G' = Functor G'
  field
    θ     : ∀ x → D.Hom (G.F₀ x) (G'.F₀ x)
    θ-iso : ∀ x → D.IsIso (θ x)
    nat   : ∀ {x y} (f : C.Hom x y) → θ y D.∘ G.F₁ f ≡ G'.F₁ f D.∘ θ x

module _ {C D : Cat} where
  private
    module C = Cat C
    module D = Cat D
    open CR D

  ni-id : ∀ (G : Functor C D) → NatIso G G
  ni-id G = record { θ = λ _ → D.id ; θ-iso = λ _ → id-iso
                   ; nat = λ f → trans (D.idl _) (sym (D.idr _)) }

  ni-∘ : ∀ {G G' G'' : Functor C D} → NatIso G' G'' → NatIso G G' → NatIso G G''
  ni-∘ {G} {G'} {G''} m n = record
    { θ = λ x → M.θ x D.∘ N.θ x
    ; θ-iso = λ x → iso-∘ (M.θ-iso x) (N.θ-iso x)
    ; nat = λ {x} {y} f →
        (M.θ y D.∘ N.θ y) D.∘ Functor.F₁ G f       ≡⟨ D.assoc _ _ _ ⟩
        M.θ y D.∘ (N.θ y D.∘ Functor.F₁ G f)       ≡⟨ congʳ _ (N.nat f) ⟩
        M.θ y D.∘ (Functor.F₁ G' f D.∘ N.θ x)      ≡⟨ sym (D.assoc _ _ _) ⟩
        (M.θ y D.∘ Functor.F₁ G' f) D.∘ N.θ x      ≡⟨ congˡ _ (M.nat f) ⟩
        (Functor.F₁ G'' f D.∘ M.θ x) D.∘ N.θ x     ≡⟨ D.assoc _ _ _ ⟩
        Functor.F₁ G'' f D.∘ (M.θ x D.∘ N.θ x) ∎ }
    where
    module M = NatIso m
    module N = NatIso n

  ni-inv : ∀ {G G' : Functor C D} → NatIso G G' → NatIso G' G
  ni-inv {G} {G'} n = record
    { θ = λ x → D.IsIso.inv (N.θ-iso x)
    ; θ-iso = λ x → inv-iso (N.θ-iso x)
    ; nat = λ {x} {y} f →
        let ix = N.θ-iso x ; iy = N.θ-iso y
            xi = D.IsIso.inv ix ; yi = D.IsIso.inv iy in
        yi D.∘ Functor.F₁ G' f                          ≡⟨ sym (D.idr _) ⟩
        (yi D.∘ Functor.F₁ G' f) D.∘ D.id               ≡⟨ congʳ _ (sym (D.IsIso.right ix)) ⟩
        (yi D.∘ Functor.F₁ G' f) D.∘ (N.θ x D.∘ xi)     ≡⟨ D.assoc _ _ _ ⟩
        yi D.∘ (Functor.F₁ G' f D.∘ (N.θ x D.∘ xi))     ≡⟨ congʳ yi (sym (D.assoc _ _ _)) ⟩
        yi D.∘ ((Functor.F₁ G' f D.∘ N.θ x) D.∘ xi)     ≡⟨ congʳ yi (congˡ xi (sym (N.nat f))) ⟩
        yi D.∘ ((N.θ y D.∘ Functor.F₁ G f) D.∘ xi)      ≡⟨ congʳ yi (D.assoc _ _ _) ⟩
        yi D.∘ (N.θ y D.∘ (Functor.F₁ G f D.∘ xi))      ≡⟨ sym (D.assoc _ _ _) ⟩
        (yi D.∘ N.θ y) D.∘ (Functor.F₁ G f D.∘ xi)      ≡⟨ congˡ _ (D.IsIso.left iy) ⟩
        D.id D.∘ (Functor.F₁ G f D.∘ xi)                ≡⟨ D.idl _ ⟩
        Functor.F₁ G f D.∘ xi ∎ }
    where module N = NatIso n

-- Whiskering.
whiskerL : ∀ {B C D} (H : Functor C D) {G G' : Functor B C}
         → NatIso G G' → NatIso (H ∘F G) (H ∘F G')
whiskerL {B} {C} {D} H {G} {G'} n = record
  { θ = λ x → H.F₁ (N.θ x)
  ; θ-iso = λ x → F-iso H (N.θ-iso x)
  ; nat = λ f → trans (sym (H.F-∘ _ _)) (trans (cong H.F₁ (N.nat f)) (H.F-∘ _ _)) }
  where
  module H = Functor H
  module N = NatIso n

whiskerR : ∀ {B C D} {G G' : Functor C D} → NatIso G G' → (K : Functor B C)
         → NatIso (G ∘F K) (G' ∘F K)
whiskerR n K = record { θ = λ x → N.θ (Functor.F₀ K x) ; θ-iso = λ x → N.θ-iso _
                      ; nat = λ f → N.nat (Functor.F₁ K f) }
  where module N = NatIso n

-- Re-association (the two functors agree on objects and arrows).
assocNI : ∀ {A B C D} (G : Functor C D) (H : Functor B C) (K : Functor A B)
        → NatIso ((G ∘F H) ∘F K) (G ∘F (H ∘F K))
assocNI {D = D} G H K = record
  { θ = λ _ → Cat.id D ; θ-iso = λ _ → CR.id-iso D
  ; nat = λ f → trans (Cat.idl D _) (sym (Cat.idr D _)) }

assocNI⁻ : ∀ {A B C D} (G : Functor C D) (H : Functor B C) (K : Functor A B)
         → NatIso (G ∘F (H ∘F K)) ((G ∘F H) ∘F K)
assocNI⁻ {D = D} G H K = record
  { θ = λ _ → Cat.id D ; θ-iso = λ _ → CR.id-iso D
  ; nat = λ f → trans (Cat.idl D _) (sym (Cat.idr D _)) }

unitLR : ∀ {C D} (G : Functor C D) → NatIso (idF ∘F G) (G ∘F idF)
unitLR {D = D} G = record
  { θ = λ _ → Cat.id D ; θ-iso = λ _ → CR.id-iso D
  ; nat = λ f → trans (Cat.idl D _) (sym (Cat.idr D _)) }

------------------------------------------------------------------------
-- Vectors and componentwise arrows.

data Vec (X : Set) : Nat → Set where
  []  : Vec X zero
  _∷_ : ∀ {n} → X → Vec X n → Vec X (suc n)

vmap : ∀ {X Y : Set} {n} → (X → Y) → Vec X n → Vec Y n
vmap f []       = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

module V (C : Cat) where
  open Cat C
  open CR C

  VH : ∀ {n} → Vec Ob n → Vec Ob n → Set
  VH []       []       = ⊤
  VH (x ∷ xs) (y ∷ ys) = Hom x y × VH xs ys

  vid : ∀ {n} {xs : Vec Ob n} → VH xs xs
  vid {xs = []}     = tt
  vid {xs = x ∷ xs} = id , vid {xs = xs}

  v∘ : ∀ {n} {xs ys zs : Vec Ob n} → VH ys zs → VH xs ys → VH xs zs
  v∘ {xs = []}     {[]}     {[]}     _        _        = tt
  v∘ {xs = _ ∷ xs} {_ ∷ ys} {_ ∷ zs} (g , gs) (f , fs) = (g ∘ f) , v∘ {xs = xs} {ys} {zs} gs fs

  vidl : ∀ {n} {xs ys : Vec Ob n} (fs : VH xs ys) → v∘ {xs = xs} {ys} {ys} (vid {xs = ys}) fs ≡ fs
  vidl {xs = []}     {[]}     fs       = refl
  vidl {xs = _ ∷ xs} {_ ∷ ys} (f , fs) = cong₂ _,_ (idl f) (vidl {xs = xs} {ys} fs)

  vidr : ∀ {n} {xs ys : Vec Ob n} (fs : VH xs ys) → v∘ {xs = xs} {xs} {ys} fs (vid {xs = xs}) ≡ fs
  vidr {xs = []}     {[]}     fs       = refl
  vidr {xs = _ ∷ xs} {_ ∷ ys} (f , fs) = cong₂ _,_ (idr f) (vidr {xs = xs} {ys} fs)

  vassoc : ∀ {n} {ws xs ys zs : Vec Ob n} (hs : VH ys zs) (gs : VH xs ys) (fs : VH ws xs)
         → v∘ {xs = ws} {xs} {zs} (v∘ {xs = xs} {ys} {zs} hs gs) fs
           ≡ v∘ {xs = ws} {ys} {zs} hs (v∘ {xs = ws} {xs} {ys} gs fs)
  vassoc {ws = []}     {[]}     {[]}     {[]}     hs gs fs = refl
  vassoc {ws = _ ∷ ws} {_ ∷ xs} {_ ∷ ys} {_ ∷ zs} (h , hs) (g , gs) (f , fs) =
    cong₂ _,_ (assoc h g f) (vassoc {ws = ws} {xs} {ys} {zs} hs gs fs)

------------------------------------------------------------------------
-- The polynomial endofunctor of a finitary signature.

module Sig (Op : Set) (A : Op → Cat) (ar : Op → Nat) where

  private
    module A i = Cat (A i)

  module P (X : Cat) where
    private
      module X = Cat X
      open V X

    POb : Set
    POb = Σ Op (λ i → A.Ob i × Vec X.Ob (ar i))

    PH : ∀ {i j} → i ≡ j → A.Ob i → A.Ob j → Vec X.Ob (ar i) → Vec X.Ob (ar j) → Set
    PH {i} refl a b xs ys = A.Hom i a b × VH xs ys

    PHom : POb → POb → Set
    PHom (i , a , xs) (j , b , ys) = Σ (i ≡ j) (λ p → PH p a b xs ys)

    pid : ∀ {x} → PHom x x
    pid {i , a , xs} = refl , (A.id i , vid {xs = xs})

    p∘ : ∀ {x y z} → PHom y z → PHom x y → PHom x z
    p∘ {i , a , xs} {.i , b , ys} {.i , c , zs} (refl , (g , gs)) (refl , (f , fs)) =
      refl , (A._∘_ i g f , v∘ {xs = xs} {ys} {zs} gs fs)

    pidl : ∀ {x y} (f : PHom x y) → p∘ {x} {y} {y} (pid {y}) f ≡ f
    pidl {i , a , xs} {.i , b , ys} (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.idl i f) (vidl {xs = xs} {ys} fs))

    pidr : ∀ {x y} (f : PHom x y) → p∘ {x} {x} {y} f (pid {x}) ≡ f
    pidr {i , a , xs} {.i , b , ys} (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.idr i f) (vidr {xs = xs} {ys} fs))

    passoc : ∀ {w x y z} (h : PHom y z) (g : PHom x y) (f : PHom w x)
           → p∘ {w} {x} {z} (p∘ {x} {y} {z} h g) f ≡ p∘ {w} {y} {z} h (p∘ {w} {x} {y} g f)
    passoc {i , _ , ws} {.i , _ , xs} {.i , _ , ys} {.i , _ , zs}
           (refl , (h , hs)) (refl , (g , gs)) (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.assoc i h g f) (vassoc {ws = ws} {xs} {ys} {zs} hs gs fs))

    PC : Cat
    PC = record
      { Ob = POb ; Hom = PHom ; id = λ {x} → pid {x}
      ; _∘_ = λ {x} {y} {z} g f → p∘ {x} {y} {z} g f
      ; idl = λ {x} {y} f → pidl {x} {y} f ; idr = λ {x} {y} f → pidr {x} {y} f
      ; assoc = λ {w} {x} {y} {z} h g f → passoc {w} {x} {y} {z} h g f }

  open P using (PC)

  -- P on functors.
  module PF {X Y : Cat} (F : Functor X Y) where
    private
      module X = Cat X
      module Y = Cat Y
      module F = Functor F
      module VX = V X
      module VY = V Y

    vF : ∀ {n} {xs ys : Vec X.Ob n} → VX.VH xs ys → VY.VH (vmap F.F₀ xs) (vmap F.F₀ ys)
    vF {xs = []}     {[]}     _        = tt
    vF {xs = _ ∷ xs} {_ ∷ ys} (f , fs) = F.F₁ f , vF {xs = xs} {ys} fs

    vF-id : ∀ {n} {xs : Vec X.Ob n} → vF {xs = xs} {xs} (VX.vid {xs = xs}) ≡ VY.vid {xs = vmap F.F₀ xs}
    vF-id {xs = []}     = refl
    vF-id {xs = _ ∷ xs} = cong₂ _,_ F.F-id (vF-id {xs = xs})

    vF-∘ : ∀ {n} {xs ys zs : Vec X.Ob n} (gs : VX.VH ys zs) (fs : VX.VH xs ys)
         → vF {xs = xs} {zs} (VX.v∘ {xs = xs} {ys} {zs} gs fs)
           ≡ VY.v∘ {xs = vmap F.F₀ xs} {vmap F.F₀ ys} {vmap F.F₀ zs} (vF {xs = ys} {zs} gs) (vF {xs = xs} {ys} fs)
    vF-∘ {xs = []}     {[]}     {[]}     _        _        = refl
    vF-∘ {xs = _ ∷ xs} {_ ∷ ys} {_ ∷ zs} (g , gs) (f , fs) =
      cong₂ _,_ (F.F-∘ g f) (vF-∘ {xs = xs} {ys} {zs} gs fs)

    P₀ : P.POb X → P.POb Y
    P₀ (i , a , xs) = i , a , vmap F.F₀ xs

    P₁ : ∀ {x y} → P.PHom X x y → P.PHom Y (P₀ x) (P₀ y)
    P₁ {i , a , xs} {.i , b , ys} (refl , (u , fs)) = refl , (u , vF {xs = xs} {ys} fs)

    Pf : Functor (PC X) (PC Y)
    Pf = record
      { F₀ = P₀ ; F₁ = λ {x} {y} → P₁ {x} {y}
      ; F-id = λ { {i , a , xs} → cong (λ q → refl , q) (cong (λ q → A.id i , q) (vF-id {xs = xs})) }
      ; F-∘ = λ { {i , _ , xs} {.i , _ , ys} {.i , _ , zs} (refl , (g , gs)) (refl , (f , fs)) →
                  cong (λ q → refl , q) (cong (λ q → A._∘_ i g f , q) (vF-∘ {xs = xs} {ys} {zs} gs fs)) } }

  open PF using (Pf)

  -- Componentwise identity arrows between vectors that agree
  -- elementwise by reduction.  Used for Pf (G ∘ H) ≅ Pf G ∘ Pf H and
  -- Pf id ≅ id.
  module _ {X : Cat} where
    private
      module X = Cat X
      module VX = V X

    -- vmap (g ∘ h) xs and vmap g (vmap h xs).
    vcmp : ∀ {Z : Set} (g : Z → X.Ob) {W : Set} (h : W → Z) {n} (ws : Vec W n)
         → VX.VH (vmap (λ w → g (h w)) ws) (vmap g (vmap h ws))
    vcmp g h []       = tt
    vcmp g h (w ∷ ws) = X.id , vcmp g h ws

    vcmp⁻ : ∀ {Z : Set} (g : Z → X.Ob) {W : Set} (h : W → Z) {n} (ws : Vec W n)
          → VX.VH (vmap g (vmap h ws)) (vmap (λ w → g (h w)) ws)
    vcmp⁻ g h []       = tt
    vcmp⁻ g h (w ∷ ws) = X.id , vcmp⁻ g h ws

    vidv : ∀ {n} (xs : Vec X.Ob n) → VX.VH (vmap (λ x → x) xs) xs
    vidv []       = tt
    vidv (x ∷ xs) = X.id , vidv xs

    vidv⁻ : ∀ {n} (xs : Vec X.Ob n) → VX.VH xs (vmap (λ x → x) xs)
    vidv⁻ []       = tt
    vidv⁻ (x ∷ xs) = X.id , vidv⁻ xs

  -- Pf (G ∘ H) ≅ Pf G ∘ Pf H.
  Pcomp : ∀ {X Y Z : Cat} (G : Functor Y Z) (H : Functor X Y)
        → NatIso (Pf (G ∘F H)) (Pf G ∘F Pf H)
  Pcomp {X} {Y} {Z} G H = record { θ = th ; θ-iso = th-iso ; nat = λ {x} {y} f → th-nat {x} {y} f }
    where
    module X = Cat X
    module Z = Cat Z
    module G = Functor G
    module H = Functor H
    module VZ = V Z
    module VX = V X
    PZ = PC Z
    module PZ = Cat PZ
    th : ∀ x → PZ.Hom (Functor.F₀ (Pf (G ∘F H)) x) (Functor.F₀ (Pf G ∘F Pf H) x)
    th (i , a , xs) = refl , (A.id i , vcmp G.F₀ H.F₀ xs)
    th⁻ : ∀ x → PZ.Hom (Functor.F₀ (Pf G ∘F Pf H) x) (Functor.F₀ (Pf (G ∘F H)) x)
    th⁻ (i , a , xs) = refl , (A.id i , vcmp⁻ G.F₀ H.F₀ xs)
    l : ∀ {n} (xs : Vec X.Ob n)
      → VZ.v∘ {xs = vmap (λ w → G.F₀ (H.F₀ w)) xs} {vmap G.F₀ (vmap H.F₀ xs)} {vmap (λ w → G.F₀ (H.F₀ w)) xs}
              (vcmp⁻ G.F₀ H.F₀ xs) (vcmp G.F₀ H.F₀ xs) ≡ VZ.vid
    l []       = refl
    l (x ∷ xs) = cong₂ _,_ (Z.idl _) (l xs)
    r : ∀ {n} (xs : Vec X.Ob n)
      → VZ.v∘ {xs = vmap G.F₀ (vmap H.F₀ xs)} {vmap (λ w → G.F₀ (H.F₀ w)) xs} {vmap G.F₀ (vmap H.F₀ xs)}
              (vcmp G.F₀ H.F₀ xs) (vcmp⁻ G.F₀ H.F₀ xs) ≡ VZ.vid
    r []       = refl
    r (x ∷ xs) = cong₂ _,_ (Z.idl _) (r xs)
    th-iso : ∀ x → PZ.IsIso (th x)
    th-iso (i , a , xs) = record
      { inv = th⁻ (i , a , xs)
      ; left = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (l xs))
      ; right = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (r xs)) }
    vn : ∀ {n} {xs ys : Vec X.Ob n} (fs : VX.VH xs ys)
       → VZ.v∘ {xs = vmap (λ w → G.F₀ (H.F₀ w)) xs} {vmap (λ w → G.F₀ (H.F₀ w)) ys} {vmap G.F₀ (vmap H.F₀ ys)}
               (vcmp G.F₀ H.F₀ ys) (PF.vF (G ∘F H) {xs = xs} {ys} fs)
         ≡ VZ.v∘ {xs = vmap (λ w → G.F₀ (H.F₀ w)) xs} {vmap G.F₀ (vmap H.F₀ xs)} {vmap G.F₀ (vmap H.F₀ ys)}
               (PF.vF G {xs = vmap H.F₀ xs} {vmap H.F₀ ys} (PF.vF H {xs = xs} {ys} fs)) (vcmp G.F₀ H.F₀ xs)
    vn {xs = []}     {[]}     _        = refl
    vn {xs = _ ∷ xs} {_ ∷ ys} (f , fs) = cong₂ _,_ (trans (Z.idl _) (sym (Z.idr _))) (vn {xs = xs} {ys} fs)
    th-nat : ∀ {x y} (f : P.PHom X x y)
           → PZ._∘_ {Functor.F₀ (Pf (G ∘F H)) x} {Functor.F₀ (Pf (G ∘F H)) y} {Functor.F₀ (Pf G ∘F Pf H) y}
               (th y) (Functor.F₁ (Pf (G ∘F H)) {x} {y} f)
             ≡ PZ._∘_ {Functor.F₀ (Pf (G ∘F H)) x} {Functor.F₀ (Pf G ∘F Pf H) x} {Functor.F₀ (Pf G ∘F Pf H) y}
               (Functor.F₁ (Pf G ∘F Pf H) {x} {y} f) (th x)
    th-nat {i , a , xs} {.i , b , ys} (refl , (u , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (trans (A.idl i u) (sym (A.idr i u))) (vn {xs = xs} {ys} fs))

  -- Pf id ≅ id.
  Pid : ∀ {X : Cat} → NatIso (Pf (idF {X})) idF
  Pid {X} = record { θ = th ; θ-iso = th-iso ; nat = λ {x} {y} f → th-nat {x} {y} f }
    where
    module X = Cat X
    module VX = V X
    PX = PC X
    module PX = Cat PX
    th : ∀ x → PX.Hom (Functor.F₀ (Pf (idF {X})) x) x
    th (i , a , xs) = refl , (A.id i , vidv xs)
    th⁻ : ∀ x → PX.Hom x (Functor.F₀ (Pf (idF {X})) x)
    th⁻ (i , a , xs) = refl , (A.id i , vidv⁻ xs)
    l : ∀ {n} (xs : Vec X.Ob n)
      → VX.v∘ {xs = vmap (λ x → x) xs} {xs} {vmap (λ x → x) xs} (vidv⁻ xs) (vidv xs) ≡ VX.vid
    l []       = refl
    l (x ∷ xs) = cong₂ _,_ (X.idl _) (l xs)
    r : ∀ {n} (xs : Vec X.Ob n)
      → VX.v∘ {xs = xs} {vmap (λ x → x) xs} {xs} (vidv xs) (vidv⁻ xs) ≡ VX.vid
    r []       = refl
    r (x ∷ xs) = cong₂ _,_ (X.idl _) (r xs)
    th-iso : ∀ x → PX.IsIso (th x)
    th-iso (i , a , xs) = record
      { inv = th⁻ (i , a , xs)
      ; left = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (l xs))
      ; right = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (r xs)) }
    vn : ∀ {n} {xs ys : Vec X.Ob n} (fs : VX.VH xs ys)
       → VX.v∘ {xs = vmap (λ x → x) xs} {vmap (λ x → x) ys} {ys} (vidv ys) (PF.vF (idF {X}) {xs = xs} {ys} fs)
         ≡ VX.v∘ {xs = vmap (λ x → x) xs} {xs} {ys} fs (vidv xs)
    vn {xs = []}     {[]}     _        = refl
    vn {xs = _ ∷ xs} {_ ∷ ys} (f , fs) = cong₂ _,_ (trans (X.idl _) (sym (X.idr _))) (vn {xs = xs} {ys} fs)
    th-nat : ∀ {x y} (f : P.PHom X x y)
           → PX._∘_ {Functor.F₀ (Pf (idF {X})) x} {Functor.F₀ (Pf (idF {X})) y} {y}
               (th y) (Functor.F₁ (Pf (idF {X})) {x} {y} f)
             ≡ PX._∘_ {Functor.F₀ (Pf (idF {X})) x} {x} {y} f (th x)
    th-nat {i , a , xs} {.i , b , ys} (refl , (u , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (trans (A.idl i u) (sym (A.idr i u))) (vn {xs = xs} {ys} fs))

  ----------------------------------------------------------------------
  -- Algebras and pseudo algebra maps.

  record AlgMap (X : Cat) (α : Functor (PC X) X) (Y : Cat) (β : Functor (PC Y) Y) : Set where
    field
      fun : Functor X Y
      sq  : NatIso (fun ∘F α) (β ∘F Pf fun)

  algId : ∀ {X} (α : Functor (PC X) X) → AlgMap X α X α
  algId {X} α = record
    { fun = idF
    ; sq  = ni-∘ (whiskerL α (ni-inv (Pid {X}))) (unitLR α) }
    -- idF ∘ α ≅ α ∘ idF (identity components) ≅ α ∘ Pf idF.

  algComp : ∀ {X Y Z α β γ} → AlgMap Y β Z γ → AlgMap X α Y β → AlgMap X α Z γ
  algComp {X} {Y} {Z} {α} {β} {γ} k h = record
    { fun = K ∘F H
    ; sq  =
        ni-∘ (whiskerL γ (ni-inv (Pcomp K H)))
        (ni-∘ (assocNI γ (Pf K) (Pf H))
        (ni-∘ (whiskerR k.sq (Pf H))
        (ni-∘ (assocNI⁻ K β (Pf H))
        (ni-∘ (whiskerL K h.sq)
              (assocNI K H α))))) }
    where
    module k = AlgMap k
    module h = AlgMap h
    K = k.fun
    H = h.fun

  -- Initiality, 1-truncated and 2-categorical: every algebra receives a
  -- pseudo map, and any two pseudo endomaps are naturally isomorphic.
  record Initial (μ : Cat) (α : Functor (PC μ) μ) : Set₁ where
    field
      init : ∀ (Y : Cat) (β : Functor (PC Y) Y) → AlgMap μ α Y β
      uniq : ∀ (h h' : AlgMap μ α μ α) → NatIso (AlgMap.fun h) (AlgMap.fun h')

  ----------------------------------------------------------------------
  -- The tree category W.

  data Tree : Set where
    node : (i : Op) → A.Ob i → Vec Tree (ar i) → Tree

  mutual
    THom : Tree → Tree → Set
    THom (node i a ts) (node j b us) = Σ (i ≡ j) (λ p → TH p a b ts us)

    TH : ∀ {i j} → i ≡ j → A.Ob i → A.Ob j → Vec Tree (ar i) → Vec Tree (ar j) → Set
    TH {i} refl a b ts us = A.Hom i a b × TV ts us

    TV : ∀ {n} → Vec Tree n → Vec Tree n → Set
    TV []       []       = ⊤
    TV (t ∷ ts) (u ∷ us) = THom t u × TV ts us

  mutual
    tid : ∀ {t} → THom t t
    tid {node i a ts} = refl , (A.id i , tvid {ts = ts})

    tvid : ∀ {n} {ts : Vec Tree n} → TV ts ts
    tvid {ts = []}     = tt
    tvid {ts = t ∷ ts} = tid {t} , tvid {ts = ts}

  mutual
    t∘ : ∀ {s t u} → THom t u → THom s t → THom s u
    t∘ {node i _ ss} {node .i _ ts} {node .i _ us} (refl , (g , gs)) (refl , (f , fs)) =
      refl , (A._∘_ i g f , tv∘ {ss = ss} {ts} {us} gs fs)

    tv∘ : ∀ {n} {ss ts us : Vec Tree n} → TV ts us → TV ss ts → TV ss us
    tv∘ {ss = []}     {[]}     {[]}     _        _        = tt
    tv∘ {ss = s ∷ ss} {t ∷ ts} {u ∷ us} (g , gs) (f , fs) =
      t∘ {s} {t} {u} g f , tv∘ {ss = ss} {ts} {us} gs fs

  mutual
    tidl : ∀ {s t} (f : THom s t) → t∘ {s} {t} {t} (tid {t}) f ≡ f
    tidl {node i _ ss} {node .i _ ts} (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.idl i f) (tvidl {ss = ss} {ts} fs))

    tvidl : ∀ {n} {ss ts : Vec Tree n} (fs : TV ss ts) → tv∘ {ss = ss} {ts} {ts} (tvid {ts = ts}) fs ≡ fs
    tvidl {ss = []}     {[]}     _        = refl
    tvidl {ss = s ∷ ss} {t ∷ ts} (f , fs) = cong₂ _,_ (tidl {s} {t} f) (tvidl {ss = ss} {ts} fs)

  mutual
    tidr : ∀ {s t} (f : THom s t) → t∘ {s} {s} {t} f (tid {s}) ≡ f
    tidr {node i _ ss} {node .i _ ts} (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.idr i f) (tvidr {ss = ss} {ts} fs))

    tvidr : ∀ {n} {ss ts : Vec Tree n} (fs : TV ss ts) → tv∘ {ss = ss} {ss} {ts} fs (tvid {ts = ss}) ≡ fs
    tvidr {ss = []}     {[]}     _        = refl
    tvidr {ss = s ∷ ss} {t ∷ ts} (f , fs) = cong₂ _,_ (tidr {s} {t} f) (tvidr {ss = ss} {ts} fs)

  mutual
    tassoc : ∀ {r s t u} (h : THom t u) (g : THom s t) (f : THom r s)
           → t∘ {r} {s} {u} (t∘ {s} {t} {u} h g) f ≡ t∘ {r} {t} {u} h (t∘ {r} {s} {t} g f)
    tassoc {node i _ rs} {node .i _ ss} {node .i _ ts} {node .i _ us}
           (refl , (h , hs)) (refl , (g , gs)) (refl , (f , fs)) =
      cong (λ q → refl , q) (cong₂ _,_ (A.assoc i h g f) (tvassoc {rs = rs} {ss} {ts} {us} hs gs fs))

    tvassoc : ∀ {n} {rs ss ts us : Vec Tree n} (hs : TV ts us) (gs : TV ss ts) (fs : TV rs ss)
            → tv∘ {ss = rs} {ss} {us} (tv∘ {ss = ss} {ts} {us} hs gs) fs
              ≡ tv∘ {ss = rs} {ts} {us} hs (tv∘ {ss = rs} {ss} {ts} gs fs)
    tvassoc {rs = []}     {[]}     {[]}     {[]}     _        _        _        = refl
    tvassoc {rs = r ∷ rs} {s ∷ ss} {t ∷ ts} {u ∷ us} (h , hs) (g , gs) (f , fs) =
      cong₂ _,_ (tassoc {r} {s} {t} {u} h g f) (tvassoc {rs = rs} {ss} {ts} {us} hs gs fs)

  W : Cat
  W = record
    { Ob = Tree ; Hom = THom ; id = λ {t} → tid {t}
    ; _∘_ = λ {s} {t} {u} g f → t∘ {s} {t} {u} g f
    ; idl = λ {s} {t} f → tidl {s} {t} f ; idr = λ {s} {t} f → tidr {s} {t} f
    ; assoc = λ {r} {s} {t} {u} h g f → tassoc {r} {s} {t} {u} h g f }

  ----------------------------------------------------------------------
  -- W is trunc 0 when every parameter is.

  module _ (par : ∀ i → T0 (A i)) where
    private
      pg : ∀ i → IsGrpd (A i)
      pg i = fst (par i)
      pt : ∀ i → Thin (A i)
      pt i = snd (par i)

    mutual
      W-thin : ∀ {s t} (f g : THom s t) → f ≡ g
      W-thin {node i _ ss} {node .i _ ts} (refl , (f , fs)) (refl , (g , gs)) =
        cong (λ q → refl , q) (cong₂ _,_ (pt i f g) (WV-thin {ss = ss} {ts} fs gs))

      WV-thin : ∀ {n} {ss ts : Vec Tree n} (fs gs : TV ss ts) → fs ≡ gs
      WV-thin {ss = []}     {[]}     _        _        = refl
      WV-thin {ss = s ∷ ss} {t ∷ ts} (f , fs) (g , gs) =
        cong₂ _,_ (W-thin {s} {t} f g) (WV-thin {ss = ss} {ts} fs gs)

    mutual
      W-inv : ∀ {s t} → THom s t → THom t s
      W-inv {node i _ ss} {node .i _ ts} (refl , (f , fs)) =
        refl , (Cat.IsIso.inv (pg i f) , WV-inv {ss = ss} {ts} fs)

      WV-inv : ∀ {n} {ss ts : Vec Tree n} → TV ss ts → TV ts ss
      WV-inv {ss = []}     {[]}     _        = tt
      WV-inv {ss = s ∷ ss} {t ∷ ts} (f , fs) = W-inv {s} {t} f , WV-inv {ss = ss} {ts} fs

    W-grpd : IsGrpd W
    W-grpd {s} {t} f = record
      { inv = W-inv {s} {t} f
      ; left = W-thin {s} {s} _ _
      ; right = W-thin {t} {t} _ _ }

    W-T0 : T0 W
    W-T0 = W-grpd , λ {s} {t} → W-thin {s} {t}

  ----------------------------------------------------------------------
  -- W is an algebra.

  private
    module VW = V W

  toTV : ∀ {n} {ts us : Vec Tree n} → VW.VH ts us → TV ts us
  toTV {ts = []}     {[]}     _        = tt
  toTV {ts = _ ∷ ts} {_ ∷ us} (f , fs) = f , toTV {ts = ts} {us} fs

  toTV-id : ∀ {n} {ts : Vec Tree n} → toTV {ts = ts} {ts} (VW.vid {xs = ts}) ≡ tvid {ts = ts}
  toTV-id {ts = []}     = refl
  toTV-id {ts = t ∷ ts} = cong (λ q → tid {t} , q) (toTV-id {ts = ts})

  toTV-∘ : ∀ {n} {ss ts us : Vec Tree n} (gs : VW.VH ts us) (fs : VW.VH ss ts)
         → toTV {ts = ss} {us} (VW.v∘ {xs = ss} {ts} {us} gs fs)
           ≡ tv∘ {ss = ss} {ts} {us} (toTV {ts = ts} {us} gs) (toTV {ts = ss} {ts} fs)
  toTV-∘ {ss = []}     {[]}     {[]}     _        _        = refl
  toTV-∘ {ss = s ∷ ss} {t ∷ ts} {u ∷ us} (g , gs) (f , fs) =
    cong (λ q → t∘ {s} {t} {u} g f , q) (toTV-∘ {ss = ss} {ts} {us} gs fs)

  β₀ : P.POb W → Tree
  β₀ (i , a , ts) = node i a ts

  β₁ : ∀ {x y} → P.PHom W x y → THom (β₀ x) (β₀ y)
  β₁ {i , a , ts} {.i , b , us} (refl , (u , fs)) = refl , (u , toTV {ts = ts} {us} fs)

  β : Functor (PC W) W
  β = record
    { F₀ = β₀ ; F₁ = λ {x} {y} → β₁ {x} {y}
    ; F-id = λ { {i , a , ts} → cong (λ q → refl , q) (cong (λ q → A.id i , q) (toTV-id {ts = ts})) }
    ; F-∘ = λ { {i , _ , ss} {.i , _ , ts} {.i , _ , us} (refl , (g , gs)) (refl , (f , fs)) →
                cong (λ q → refl , q) (cong (λ q → A._∘_ i g f , q) (toTV-∘ {ss = ss} {ts} {us} gs fs)) } }

  ----------------------------------------------------------------------
  -- The map s : W → μ for an algebra (μ, α).

  module S (μ : Cat) (α : Functor (PC μ) μ) where
    private
      module μ = Cat μ
      module α = Functor α
      module Vμ = V μ
      Pμ = PC μ
      module Pμ = Cat Pμ

    mutual
      s₀ : Tree → μ.Ob
      s₀ (node i a ts) = α.F₀ (i , a , smap ts)

      smap : ∀ {n} → Vec Tree n → Vec μ.Ob n
      smap []       = []
      smap (t ∷ ts) = s₀ t ∷ smap ts

    mutual
      s₁ : ∀ {s t} → THom s t → μ.Hom (s₀ s) (s₀ t)
      s₁ {node i a ss} {node .i b ts} (refl , (u , fs)) =
        α.F₁ {i , a , smap ss} {i , b , smap ts} (refl , (u , sV {ss = ss} {ts} fs))

      sV : ∀ {n} {ss ts : Vec Tree n} → TV ss ts → Vμ.VH (smap ss) (smap ts)
      sV {ss = []}     {[]}     _        = tt
      sV {ss = s ∷ ss} {t ∷ ts} (f , fs) = s₁ {s} {t} f , sV {ss = ss} {ts} fs

    mutual
      s-id : ∀ {t} → s₁ {t} {t} (tid {t}) ≡ μ.id
      s-id {node i a ts} =
        trans (cong (λ q → α.F₁ {i , a , smap ts} {i , a , smap ts} (refl , (A.id i , q)))
                    (sV-id {ts = ts}))
              α.F-id

      sV-id : ∀ {n} {ts : Vec Tree n} → sV {ss = ts} {ts} (tvid {ts = ts}) ≡ Vμ.vid {xs = smap ts}
      sV-id {ts = []}     = refl
      sV-id {ts = t ∷ ts} = cong₂ _,_ (s-id {t}) (sV-id {ts = ts})

    mutual
      s-∘ : ∀ {r s t} (g : THom s t) (f : THom r s)
          → s₁ {r} {t} (t∘ {r} {s} {t} g f) ≡ s₁ {s} {t} g μ.∘ s₁ {r} {s} f
      s-∘ {node i a rs} {node .i b ss} {node .i c ts} (refl , (g , gs)) (refl , (f , fs)) =
        trans (cong (λ q → α.F₁ {i , a , smap rs} {i , c , smap ts} (refl , (A._∘_ i g f , q)))
                    (sV-∘ {rs = rs} {ss} {ts} gs fs))
              (α.F-∘ {i , a , smap rs} {i , b , smap ss} {i , c , smap ts}
                     (refl , (g , sV {ss = ss} {ts} gs)) (refl , (f , sV {ss = rs} {ss} fs)))

      sV-∘ : ∀ {n} {rs ss ts : Vec Tree n} (gs : TV ss ts) (fs : TV rs ss)
           → sV {ss = rs} {ts} (tv∘ {ss = rs} {ss} {ts} gs fs)
             ≡ Vμ.v∘ {xs = smap rs} {smap ss} {smap ts} (sV {ss = ss} {ts} gs) (sV {ss = rs} {ss} fs)
      sV-∘ {rs = []}     {[]}     {[]}     _        _        = refl
      sV-∘ {rs = r ∷ rs} {s ∷ ss} {t ∷ ts} (g , gs) (f , fs) =
        cong₂ _,_ (s-∘ {r} {s} {t} g f) (sV-∘ {rs = rs} {ss} {ts} gs fs)

    sF : Functor W μ
    sF = record { F₀ = s₀ ; F₁ = λ {s} {t} → s₁ {s} {t}
                ; F-id = λ {t} → s-id {t} ; F-∘ = λ {r} {s} {t} g f → s-∘ {r} {s} {t} g f }

    -- s is a pseudo algebra map: s ∘ β ≅ α ∘ Pf s.  Components are α
    -- applied to componentwise identities between smap ts and
    -- vmap s₀ ts.
    private
      sm : ∀ {n} (ts : Vec Tree n) → Vμ.VH (smap ts) (vmap s₀ ts)
      sm []       = tt
      sm (t ∷ ts) = μ.id , sm ts

      sm⁻ : ∀ {n} (ts : Vec Tree n) → Vμ.VH (vmap s₀ ts) (smap ts)
      sm⁻ []       = tt
      sm⁻ (t ∷ ts) = μ.id , sm⁻ ts

      sm-l : ∀ {n} (ts : Vec Tree n)
           → Vμ.v∘ {xs = smap ts} {vmap s₀ ts} {smap ts} (sm⁻ ts) (sm ts) ≡ Vμ.vid
      sm-l []       = refl
      sm-l (t ∷ ts) = cong₂ _,_ (μ.idl _) (sm-l ts)

      sm-r : ∀ {n} (ts : Vec Tree n)
           → Vμ.v∘ {xs = vmap s₀ ts} {smap ts} {vmap s₀ ts} (sm ts) (sm⁻ ts) ≡ Vμ.vid
      sm-r []       = refl
      sm-r (t ∷ ts) = cong₂ _,_ (μ.idl _) (sm-r ts)

      i₀ : P.POb W → P.POb μ
      i₀ (i , a , ts) = i , a , smap ts
      j₀ : P.POb W → P.POb μ
      j₀ (i , a , ts) = i , a , vmap s₀ ts
      θP : ∀ x → Pμ.Hom (i₀ x) (j₀ x)
      θP (i , a , ts) = refl , (A.id i , sm ts)

      θP-iso : ∀ x → Pμ.IsIso (θP x)
      θP-iso (i , a , ts) = record
        { inv = refl , (A.id i , sm⁻ ts)
        ; left = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (sm-l ts))
        ; right = cong (λ q → refl , q) (cong₂ _,_ (A.idl i _) (sm-r ts)) }

      vn : ∀ {n} {ss ts : Vec Tree n} (fs : VW.VH ss ts)
         → Vμ.v∘ {xs = smap ss} {smap ts} {vmap s₀ ts} (sm ts) (sV {ss = ss} {ts} (toTV {ts = ss} {ts} fs))
           ≡ Vμ.v∘ {xs = smap ss} {vmap s₀ ss} {vmap s₀ ts} (PF.vF sF {xs = ss} {ts} fs) (sm ss)
      vn {ss = []}     {[]}     _        = refl
      vn {ss = s ∷ ss} {t ∷ ts} (f , fs) =
        cong₂ _,_ (trans (μ.idl _) (sym (μ.idr _))) (vn {ss = ss} {ts} fs)

    sAlg : AlgMap W β μ α
    sAlg = record
      { fun = sF
      ; sq  = record
          { θ = λ x → α.F₁ {i₀ x} {j₀ x} (θP x)
          ; θ-iso = λ x → F-iso α (θP-iso x)
          ; nat = λ {x} {y} f → nt {x} {y} f } }
      where
      nt : ∀ {x y} (f : P.PHom W x y)
         → α.F₁ {i₀ y} {j₀ y} (θP y) μ.∘ s₁ {β₀ x} {β₀ y} (β₁ {x} {y} f)
           ≡ α.F₁ {j₀ x} {j₀ y} (PF.P₁ sF {x} {y} f) μ.∘ α.F₁ {i₀ x} {j₀ x} (θP x)
      nt {i , a , ss} {.i , b , ts} (refl , (u , fs)) =
        trans (sym (α.F-∘ {i , a , smap ss} {i , b , smap ts} {i , b , vmap s₀ ts}
                          (θP (i , b , ts)) (refl , (u , sV {ss = ss} {ts} (toTV {ts = ss} {ts} fs)))))
        (trans (cong (λ q → α.F₁ {i , a , smap ss} {i , b , vmap s₀ ts} (refl , q))
                     (cong₂ _,_ (trans (A.idl i u) (sym (A.idr i u))) (vn {ss = ss} {ts} fs)))
               (α.F-∘ {i , a , smap ss} {i , a , vmap s₀ ss} {i , b , vmap s₀ ts}
                      (refl , (u , PF.vF sF {xs = ss} {ts} fs)) (θP (i , a , ss))))

  ----------------------------------------------------------------------
  -- T-init at n = 0.

  tinit : ∀ (μ : Cat) (α : Functor (PC μ) μ) → Initial μ α
        → (∀ i → T0 (A i)) → Trunc μ l0
  tinit μ α ini par = grpd , thin
    where
    module μ = Cat μ
    open CR μ
    module I = Initial ini
    hA : AlgMap μ α W β
    hA = I.init W β
    module S' = S μ α
    shA : AlgMap μ α μ α
    shA = algComp S'.sAlg hA
    H = AlgMap.fun hA
    module H = Functor H
    module SF = Functor S'.sF
    ν : NatIso (AlgMap.fun shA) idF
    ν = I.uniq shA (algId α)
    module ν = NatIso ν

    -- f = θ_y ∘ s(h f) ∘ θ_x⁻¹.
    rep : ∀ {x y} (f : μ.Hom x y) → f ≡ (ν.θ y μ.∘ SF.F₁ (H.F₁ f)) μ.∘ μ.IsIso.inv (ν.θ-iso x)
    rep {x} {y} f = conj (ν.θ-iso x) (ν.nat f)

    thin : Thin μ
    thin {x} {y} f g =
      trans (rep f)
        (trans (cong (λ k → (ν.θ y μ.∘ SF.F₁ k) μ.∘ μ.IsIso.inv (ν.θ-iso x))
                     (W-thin par {H.F₀ x} {H.F₀ y} (H.F₁ f) (H.F₁ g)))
               (sym (rep g)))

    grpd : IsGrpd μ
    grpd {x} {y} f =
      subst μ.IsIso (sym (rep f))
        (iso-∘ (iso-∘ (ν.θ-iso y) (F-iso S'.sF (W-grpd par {H.F₀ x} {H.F₀ y} (H.F₁ f))))
               (inv-iso (ν.θ-iso x)))

  ----------------------------------------------------------------------
  -- The hypothesis is satisfiable: with trunc 0 parameters, W itself is
  -- initial in the sense above.

  module _ (par : ∀ i → T0 (A i)) where
    private
      module WC = Cat W

      -- For a pseudo endomap h of W, an arrow h t → t, by induction.
      module K (h : AlgMap W β W β) where
        private
          module h = AlgMap h
          module hF = Functor h.fun
          module hs = NatIso h.sq
        mutual
          k : ∀ t → THom (hF.F₀ t) t
          k (node i a ts) =
            t∘ {hF.F₀ (node i a ts)} {node i a (vmap hF.F₀ ts)} {node i a ts}
               (refl , (A.id i , kv ts)) (hs.θ (i , a , ts))

          kv : ∀ {n} (ts : Vec Tree n) → TV (vmap hF.F₀ ts) ts
          kv []       = tt
          kv (t ∷ ts) = k t , kv ts

    W-initial : Initial W β
    W-initial = record
      { init = λ Y β' → S.sAlg Y β'
      ; uniq = λ h h' → record
          { θ = λ t → t∘ {Functor.F₀ (AlgMap.fun h) t} {t} {Functor.F₀ (AlgMap.fun h') t}
                         (W-inv par {Functor.F₀ (AlgMap.fun h') t} {t} (K.k h' t)) (K.k h t)
          ; θ-iso = λ t → W-grpd par _
          ; nat = λ {x} {y} f → W-thin par _ _ } }

  -- n ≥ 1: vacuous in 1-categories.
  tinit-≥1 : ∀ (μ : Cat) → Trunc μ l1
  tinit-≥1 μ = tt
