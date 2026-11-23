------------------------------------------------------------------------
-- Ledger F10f, part 5 (notes/universe-free-principles.md §6a, "T-hom⁻ is
-- not derivable").
--
-- The countermodel, 1-truncated.  Reinterpret the judgment
-- `C trunc n` as
--     trunc′ C n  :=  Trunc C n  ×  C is a groupoid,
-- i.e. "n-truncated groupoid".  Every rule that concludes `trunc`,
-- except T-hom⁻, stays sound under this reading (argued in the note; partly checked below), and T-hom⁻ fails on
-- the walking arrow I = ⟦D¹⟧.  So T-hom⁻ is not derivable from the
-- other rules, and neither is T-graph's one-edge instance
-- ⟦D¹⟧ trunc 1: without T-hom⁻ no non-groupoid is ever trunc n.
--
-- Levels.  In 1-categories (CocartLemmas.Cat: hom-sets, K) the levels
-- are −2, −1, 0 and "≥ 1"; every 1-category is trunc n for n ≥ 1.
--   Trunc C ≥1 = ⊤
--   Trunc C 0  = C is a groupoid and parallel arrows are equal
--   Trunc C −1 = Trunc C 0 and any two objects have an arrow
--   Trunc C −2 = Trunc C −1 and C has an object
--
-- What is machine-checked (for trunc′):
--   * use rules: trunc′ ⟹ Trunc (`trunc′⇒Trunc`), so T-fill, T-inv and
--     T-ctr, which consume `trunc`, stay sound;
--   * T-cum (`cum′`);
--   * T-unit: the terminal category is trunc′ −2, the empty one
--     trunc′ −1 (`unit′`, `empty′`);
--   * T-lim, only for products (`prod′`) and comma objects (`comma′`).
--     With the apex a groupoid, comma objects give pseudo-pullbacks and
--     the arrow category [I, G].  Equalisers, other finite limits and
--     weighted/lax limits are not encoded;
--   * T-hom: hom-sets, as discrete categories, are trunc′ (n − 1)
--     (`hom′`, for n = ≥1, 0, −1; its groupoid half is trivial here,
--     since discrete categories are groupoids);
--   * T-coprod: coproducts at n ≥ 0 (`coprod′`);
--   * T-hom⁻ fails: I is not trunc′ ≥1 (`I-not-trunc′`), because its
--     arrow is not invertible.  T-hom⁻'s premise (relative truncation
--     of (s, t) : [I, I] → I × I) is NOT encoded.  `I-homs′` only records
--     that I's hom-sets, as discrete categories, are trunc′ 0, which is
--     true of every set (`disc-l0`, `disc-grpd`).
--
-- What is NOT machine-checked.
--   * T-init under trunc′ (μΔ with groupoid parameters is a groupoid:
--     the core carries every model to a model, so μΔ is a retract of
--     its core); argued in the note, not encoded.
--   * General weighted/lax limits (cotensors [K, G] for arbitrary K
--     need function extensionality for natural transformations, which
--     --safe Agda without funext lacks).
--   * Rules that only consume `trunc` (T-fill, T-inv, T-ctr, DESC-tr)
--     stay sound because trunc′ is stronger than trunc.  INIT's carrier
--     marks are reread as trunc′ (they also produce trunc, via T-trunc);
--     that the reread class is reflective and closed under limits and
--     filtered colimits is argued, not encoded.
--   * The relative judgment `p relatively trunc n` is not encoded.
--   * The ω-categorical model: this is its 1-truncated shadow.
------------------------------------------------------------------------
module CaTTExp.Descent.TruncGrpdModel where

open import CaTTExp.Prelude
open import CaTTExp.Descent.CocartLemmas
open import CaTTExp.Descent.Collage using (I; IOb; o0; o1; IHom)
open import CaTTExp.Descent.RelCollage using (Prod)

------------------------------------------------------------------------
-- Truncation levels.

data Lvl : Set where
  m2 m1 l0 l1 : Lvl

IsGrpd : Cat → Set
IsGrpd C = ∀ {x y} (f : Cat.Hom C x y) → Cat.IsIso C f

Thin : Cat → Set
Thin C = ∀ {x y} (f g : Cat.Hom C x y) → f ≡ g

T0 : Cat → Set
T0 C = IsGrpd C × Thin C

Conn : Cat → Set
Conn C = ∀ x y → Cat.Hom C x y

Trunc : Cat → Lvl → Set
Trunc C l1 = ⊤
Trunc C l0 = T0 C
Trunc C m1 = T0 C × Conn C
Trunc C m2 = (T0 C × Conn C) × Cat.Ob C

trunc′ : Cat → Lvl → Set
trunc′ C n = Trunc C n × IsGrpd C

trunc′⇒Trunc : ∀ {C n} → trunc′ C n → Trunc C n
trunc′⇒Trunc = fst

suc-l : Lvl → Lvl
suc-l m2 = m1
suc-l m1 = l0
suc-l l0 = l1
suc-l l1 = l1

pred-l : Lvl → Lvl
pred-l m2 = m2      -- unused: T-hom needs n ≥ −1
pred-l m1 = m2
pred-l l0 = m1
pred-l l1 = l0

cum : ∀ {C} n → Trunc C n → Trunc C (suc-l n)
cum m2 t = fst t
cum m1 t = fst t
cum l0 t = tt
cum l1 t = tt

cum′ : ∀ {C} n → trunc′ C n → trunc′ C (suc-l n)
cum′ n (t , g) = cum n t , g

-- Thin, connectedness and pointedness, read off the levels.
thin-of : ∀ {C} n → Trunc C n → (n ≡ l1 → ⊥) → Thin C
thin-of l1 t ne = ⊥-elim (ne refl)
thin-of l0 t ne = snd t
thin-of m1 t ne = snd (fst t)
thin-of m2 t ne = snd (fst (fst t))

------------------------------------------------------------------------
-- Helpers.

private
  Σ≡ : ∀ {X : Set} {P : X → Set} {x y : X} {px : P x} {py : P y}
     → (∀ a (p q : P a) → p ≡ q) → x ≡ y → _≡_ {A = Σ X P} (x , px) (y , py)
  Σ≡ {px = px} {py} prop refl = cong (λ p → _ , p) (prop _ px py)

  module Rs (C : Cat) where
    open Cat C
    congˡ : ∀ {x y z} {g g' : Hom y z} (f : Hom x y) → g ≡ g' → g ∘ f ≡ g' ∘ f
    congˡ f refl = refl
    congʳ : ∀ {x y z} (g : Hom y z) {f f' : Hom x y} → f ≡ f' → g ∘ f ≡ g ∘ f'
    congʳ g refl = refl

------------------------------------------------------------------------
-- T-unit.

One : Cat
One = record { Ob = ⊤ ; Hom = λ _ _ → ⊤ ; id = tt ; _∘_ = λ _ _ → tt
             ; idl = λ _ → refl ; idr = λ _ → refl ; assoc = λ _ _ _ → refl }

Zero : Cat
Zero = record { Ob = ⊥ ; Hom = λ _ _ → ⊤ ; id = tt ; _∘_ = λ _ _ → tt
              ; idl = λ _ → refl ; idr = λ _ → refl ; assoc = λ _ _ _ → refl }

private
  one-grpd : IsGrpd One
  one-grpd f = record { inv = tt ; left = refl ; right = refl }

  zero-grpd : IsGrpd Zero
  zero-grpd {x} = ⊥-elim x

unit′ : trunc′ One m2
unit′ = (((one-grpd , λ _ _ → refl) , λ _ _ → tt) , tt) , one-grpd

empty′ : trunc′ Zero m1
empty′ = ((zero-grpd , λ {x} → ⊥-elim x) , λ x → ⊥-elim x) , zero-grpd

------------------------------------------------------------------------
-- T-hom: a set as a discrete category.

Disc : Set → Cat
Disc S = record { Ob = S ; Hom = _≡_ ; id = refl ; _∘_ = λ q p → trans p q
                ; idl = λ { refl → refl } ; idr = λ { refl → refl }
                ; assoc = λ { refl refl refl → refl } }

private
  disc-grpd : ∀ S → IsGrpd (Disc S)
  disc-grpd S refl = record { inv = refl ; left = refl ; right = refl }

  disc-l0 : ∀ S → Trunc (Disc S) l0
  disc-l0 S = disc-grpd S , uip

hom′ : ∀ C n → (n ≡ m2 → ⊥) → trunc′ C n → ∀ x y → trunc′ (Disc (Cat.Hom C x y)) (pred-l n)
hom′ C m2 ne _ x y = ⊥-elim (ne refl)
hom′ C l1 ne _ x y = disc-l0 _ , disc-grpd _
hom′ C l0 ne (t , g) x y = (disc-l0 _ , snd t) , disc-grpd _
hom′ C m1 ne (t , g) x y = ((disc-l0 _ , snd (fst t)) , snd t x y) , disc-grpd _

------------------------------------------------------------------------
-- T-lim: products.

module _ (A B : Cat) where
  private
    module A = Cat A
    module B = Cat B
    AB = Prod A B

  prod-grpd : IsGrpd A → IsGrpd B → IsGrpd AB
  prod-grpd ga gb f = record
    { inv   = A.IsIso.inv (ga (fst f)) , B.IsIso.inv (gb (snd f))
    ; left  = cong₂ _,_ (A.IsIso.left (ga (fst f))) (B.IsIso.left (gb (snd f)))
    ; right = cong₂ _,_ (A.IsIso.right (ga (fst f))) (B.IsIso.right (gb (snd f))) }

  private
    p0 : T0 A → T0 B → IsGrpd A → IsGrpd B → T0 AB
    p0 (_ , ta) (_ , tb) ga gb =
      prod-grpd ga gb , λ f g → cong₂ _,_ (ta (fst f) (fst g)) (tb (snd f) (snd g))
    pc : Conn A → Conn B → Conn AB
    pc ca cb x y = ca (fst x) (fst y) , cb (snd x) (snd y)

  prod : ∀ n → Trunc A n → Trunc B n → IsGrpd A → IsGrpd B → Trunc AB n
  prod l1 _ _ _ _ = tt
  prod l0 a b ga gb = p0 a b ga gb
  prod m1 (a , ca) (b , cb) ga gb = p0 a b ga gb , pc ca cb
  prod m2 ((a , ca) , oa) ((b , cb) , ob) ga gb = (p0 a b ga gb , pc ca cb) , (oa , ob)

  prod′ : ∀ n → trunc′ A n → trunc′ B n → trunc′ AB n
  prod′ n (ta , ga) (tb , gb) = prod n ta tb ga gb , prod-grpd ga gb

------------------------------------------------------------------------
-- T-lim: comma objects f ↓ g for f : A → C ← B : g.

module _ (A B C : Cat) (f : Functor A C) (g : Functor B C) where
  private
    module A = Cat A
    module B = Cat B
    module C = Cat C
    module f = Functor f
    module g = Functor g
    open Rs C

  CmOb : Set
  CmOb = Σ A.Ob (λ a → Σ B.Ob (λ b → C.Hom (f.F₀ a) (g.F₀ b)))

  CmHom : CmOb → CmOb → Set
  CmHom (a , b , h) (a' , b' , h') =
    Σ (A.Hom a a' × B.Hom b b') (λ uv → g.F₁ (snd uv) C.∘ h ≡ h' C.∘ f.F₁ (fst uv))

  private
    cm≡ : ∀ {x y} {p q : CmHom x y} → fst p ≡ fst q → p ≡ q
    cm≡ {x} {y} {_ , _} {_ , _} e = Σ≡ (λ _ → uip) e

    cid : ∀ {x} → CmHom x x
    cid {a , b , h} = (A.id , B.id) ,
      (g.F₁ B.id C.∘ h   ≡⟨ congˡ h g.F-id ⟩
       C.id C.∘ h        ≡⟨ C.idl h ⟩
       h                 ≡⟨ sym (C.idr h) ⟩
       h C.∘ C.id        ≡⟨ congʳ h (sym f.F-id) ⟩
       h C.∘ f.F₁ A.id ∎)

    c∘ : ∀ {x y z} → CmHom y z → CmHom x y → CmHom x z
    c∘ {a , b , h} {a' , b' , h'} {a'' , b'' , h''} ((u' , v') , s') ((u , v) , s) =
      ((u' A.∘ u) , (v' B.∘ v)) ,
      (g.F₁ (v' B.∘ v) C.∘ h                  ≡⟨ congˡ h (g.F-∘ v' v) ⟩
       (g.F₁ v' C.∘ g.F₁ v) C.∘ h             ≡⟨ C.assoc _ _ _ ⟩
       g.F₁ v' C.∘ (g.F₁ v C.∘ h)             ≡⟨ congʳ (g.F₁ v') s ⟩
       g.F₁ v' C.∘ (h' C.∘ f.F₁ u)            ≡⟨ sym (C.assoc _ _ _) ⟩
       (g.F₁ v' C.∘ h') C.∘ f.F₁ u            ≡⟨ congˡ (f.F₁ u) s' ⟩
       (h'' C.∘ f.F₁ u') C.∘ f.F₁ u           ≡⟨ C.assoc _ _ _ ⟩
       h'' C.∘ (f.F₁ u' C.∘ f.F₁ u)           ≡⟨ congʳ h'' (sym (f.F-∘ u' u)) ⟩
       h'' C.∘ f.F₁ (u' A.∘ u) ∎)

  Comma : Cat
  Comma = record
    { Ob = CmOb ; Hom = CmHom
    ; id = λ {x} → cid {x}
    ; _∘_ = λ {x} {y} {z} q p → c∘ {x} {y} {z} q p
    ; idl = λ {x} {y} p → cm≡ {x} {y} (cong₂ _,_ (A.idl _) (B.idl _))
    ; idr = λ {x} {y} p → cm≡ {x} {y} (cong₂ _,_ (A.idr _) (B.idr _))
    ; assoc = λ {w} {x} {y} {z} r q p → cm≡ {w} {z} (cong₂ _,_ (A.assoc _ _ _) (B.assoc _ _ _)) }

  private
    F-inv : ∀ {D E : Cat} (F : Functor D E) {x y} {u : Cat.Hom D x y} (i : Cat.IsIso D u)
          → Cat._∘_ E (Functor.F₁ F (Cat.IsIso.inv i)) (Functor.F₁ F u) ≡ Cat.id E
    F-inv F {u = u} i = trans (sym (Functor.F-∘ F _ u))
                          (trans (cong (Functor.F₁ F) (Cat.IsIso.left i)) (Functor.F-id F))
    F-inv′ : ∀ {D E : Cat} (F : Functor D E) {x y} {u : Cat.Hom D x y} (i : Cat.IsIso D u)
           → Cat._∘_ E (Functor.F₁ F u) (Functor.F₁ F (Cat.IsIso.inv i)) ≡ Cat.id E
    F-inv′ F {u = u} i = trans (sym (Functor.F-∘ F u _))
                           (trans (cong (Functor.F₁ F) (Cat.IsIso.right i)) (Functor.F-id F))

  comma-grpd : IsGrpd A → IsGrpd B → IsGrpd Comma
  comma-grpd ga gb {a , b , h} {a' , b' , h'} ((u , v) , s) = record
    { inv   = (u⁻ , v⁻) , s⁻
    ; left  = cm≡ {a , b , h} {a , b , h} (cong₂ _,_ (A.IsIso.left iu) (B.IsIso.left iv))
    ; right = cm≡ {a' , b' , h'} {a' , b' , h'} (cong₂ _,_ (A.IsIso.right iu) (B.IsIso.right iv)) }
    where
    iu = ga u
    iv = gb v
    u⁻ = A.IsIso.inv iu
    v⁻ = B.IsIso.inv iv
    s⁻ : g.F₁ v⁻ C.∘ h' ≡ h C.∘ f.F₁ u⁻
    s⁻ =
      g.F₁ v⁻ C.∘ h'                                        ≡⟨ sym (C.idr _) ⟩
      (g.F₁ v⁻ C.∘ h') C.∘ C.id                             ≡⟨ congʳ _ (sym (F-inv′ f iu)) ⟩
      (g.F₁ v⁻ C.∘ h') C.∘ (f.F₁ u C.∘ f.F₁ u⁻)             ≡⟨ C.assoc _ _ _ ⟩
      g.F₁ v⁻ C.∘ (h' C.∘ (f.F₁ u C.∘ f.F₁ u⁻))             ≡⟨ congʳ _ (sym (C.assoc _ _ _)) ⟩
      g.F₁ v⁻ C.∘ ((h' C.∘ f.F₁ u) C.∘ f.F₁ u⁻)             ≡⟨ congʳ _ (congˡ _ (sym s)) ⟩
      g.F₁ v⁻ C.∘ ((g.F₁ v C.∘ h) C.∘ f.F₁ u⁻)              ≡⟨ congʳ _ (C.assoc _ _ _) ⟩
      g.F₁ v⁻ C.∘ (g.F₁ v C.∘ (h C.∘ f.F₁ u⁻))              ≡⟨ sym (C.assoc _ _ _) ⟩
      (g.F₁ v⁻ C.∘ g.F₁ v) C.∘ (h C.∘ f.F₁ u⁻)              ≡⟨ congˡ _ (F-inv g iv) ⟩
      C.id C.∘ (h C.∘ f.F₁ u⁻)                              ≡⟨ C.idl _ ⟩
      h C.∘ f.F₁ u⁻ ∎

  private
    k0 : T0 A → T0 B → IsGrpd A → IsGrpd B → T0 Comma
    k0 (_ , ta) (_ , tb) ga gb =
      comma-grpd ga gb , λ {x} {y} p q → cm≡ {x} {y} (cong₂ _,_ (ta _ _) (tb _ _))
    kc : Conn A → Conn B → Thin C → Conn Comma
    kc ca cb tc (x , y , h) (x' , y' , h') = (ca x x' , cb y y') , tc _ _

  comma : ∀ n → Trunc A n → Trunc B n → Trunc C n → IsGrpd A → IsGrpd B → Trunc Comma n
  comma l1 _ _ _ _ _ = tt
  comma l0 a b c ga gb = k0 a b ga gb
  comma m1 (a , ca) (b , cb) (c , cc) ga gb = k0 a b ga gb , kc ca cb (snd c)
  comma m2 ((a , ca) , oa) ((b , cb) , ob) ((c , cc) , oc) ga gb =
    (k0 a b ga gb , kc ca cb (snd c)) , (oa , ob , cc (f.F₀ oa) (g.F₀ ob))

  comma′ : ∀ n → trunc′ A n → trunc′ B n → trunc′ C n → trunc′ Comma n
  comma′ n (ta , ga) (tb , gb) (tc , gc) = comma n ta tb tc ga gb , comma-grpd ga gb

------------------------------------------------------------------------
-- T-coprod (n ≥ 0).

data _⊎_ (X Y : Set) : Set where
  inl : X → X ⊎ Y
  inr : Y → X ⊎ Y

module _ (A B : Cat) where
  private
    module A = Cat A
    module B = Cat B

  CpHom : A.Ob ⊎ B.Ob → A.Ob ⊎ B.Ob → Set
  CpHom (inl a) (inl a') = A.Hom a a'
  CpHom (inr b) (inr b') = B.Hom b b'
  CpHom _ _ = ⊥

  private
    cpid : ∀ {x} → CpHom x x
    cpid {inl _} = A.id
    cpid {inr _} = B.id

    cp∘ : ∀ {x y z} → CpHom y z → CpHom x y → CpHom x z
    cp∘ {inl _} {inl _} {inl _} g f = g A.∘ f
    cp∘ {inr _} {inr _} {inr _} g f = g B.∘ f
    cp∘ {inl _} {inl _} {inr _} () f
    cp∘ {inl _} {inr _} {_}     g ()
    cp∘ {inr _} {inl _} {_}     g ()
    cp∘ {inr _} {inr _} {inl _} () f

    cpidl : ∀ {x y} (f : CpHom x y) → cp∘ {x} {y} {y} (cpid {y}) f ≡ f
    cpidl {inl _} {inl _} f = A.idl f
    cpidl {inr _} {inr _} f = B.idl f
    cpidl {inl _} {inr _} ()
    cpidl {inr _} {inl _} ()

    cpidr : ∀ {x y} (f : CpHom x y) → cp∘ {x} {x} {y} f (cpid {x}) ≡ f
    cpidr {inl _} {inl _} f = A.idr f
    cpidr {inr _} {inr _} f = B.idr f
    cpidr {inl _} {inr _} ()
    cpidr {inr _} {inl _} ()

    cpassoc : ∀ {w x y z} (h : CpHom y z) (g : CpHom x y) (f : CpHom w x)
            → cp∘ {w} {x} {z} (cp∘ {x} {y} {z} h g) f ≡ cp∘ {w} {y} {z} h (cp∘ {w} {x} {y} g f)
    cpassoc {inl _} {inl _} {inl _} {inl _} h g f = A.assoc h g f
    cpassoc {inr _} {inr _} {inr _} {inr _} h g f = B.assoc h g f
    cpassoc {inl _} {inl _} {inl _} {inr _} () g f
    cpassoc {inl _} {inl _} {inr _} {_}     h () f
    cpassoc {inl _} {inr _} {_}     {_}     h g ()
    cpassoc {inr _} {inl _} {_}     {_}     h g ()
    cpassoc {inr _} {inr _} {inl _} {_}     h () f
    cpassoc {inr _} {inr _} {inr _} {inl _} () g f

  Coprod : Cat
  Coprod = record
    { Ob = A.Ob ⊎ B.Ob ; Hom = CpHom ; id = λ {x} → cpid {x}
    ; _∘_ = λ {x} {y} {z} g f → cp∘ {x} {y} {z} g f
    ; idl = λ {x} {y} f → cpidl {x} {y} f ; idr = λ {x} {y} f → cpidr {x} {y} f
    ; assoc = λ {w} {x} {y} {z} h g f → cpassoc {w} {x} {y} {z} h g f }

  coprod-grpd : IsGrpd A → IsGrpd B → IsGrpd Coprod
  coprod-grpd ga gb {inl _} {inl _} f = record
    { inv = A.IsIso.inv (ga f) ; left = A.IsIso.left (ga f) ; right = A.IsIso.right (ga f) }
  coprod-grpd ga gb {inr _} {inr _} f = record
    { inv = B.IsIso.inv (gb f) ; left = B.IsIso.left (gb f) ; right = B.IsIso.right (gb f) }
  coprod-grpd ga gb {inl _} {inr _} ()
  coprod-grpd ga gb {inr _} {inl _} ()

  private
    coprod-thin : Thin A → Thin B → Thin Coprod
    coprod-thin ta tb {inl _} {inl _} f g = ta f g
    coprod-thin ta tb {inr _} {inr _} f g = tb f g
    coprod-thin ta tb {inl _} {inr _} ()
    coprod-thin ta tb {inr _} {inl _} ()

  -- n ≥ 0 only: at n = −1 the coproduct of two propositions is not one.
  coprod′ : ∀ n → (n ≡ l0) ⊎ (n ≡ l1) → trunc′ A n → trunc′ B n → trunc′ Coprod n
  coprod′ .l0 (inl refl) ((_ , ta) , ga) ((_ , tb) , gb) =
    (coprod-grpd ga gb , (λ {x} {y} → coprod-thin ta tb {x} {y})) , coprod-grpd ga gb
  coprod′ .l1 (inr refl) (_ , ga) (_ , gb) = tt , coprod-grpd ga gb

------------------------------------------------------------------------
-- T-hom⁻ fails: the walking arrow.

-- Every hom of I, as a discrete category, is trunc′ 0 (true of every
-- set).  This is not T-hom⁻'s premise, which is relative and not encoded.
I-homs′ : ∀ x y → trunc′ (Disc (IHom x y)) l0
I-homs′ x y = disc-l0 _ , disc-grpd _

-- But I is not trunc′ 1: its arrow o0 → o1 has no inverse.
I-not-grpd : IsGrpd I → ⊥
I-not-grpd gI = Cat.IsIso.inv (gI {o0} {o1} tt)

I-not-trunc′ : trunc′ I l1 → ⊥
I-not-trunc′ (_ , gI) = I-not-grpd gI

-- Under the standard reading, I is trunc 1 (every 1-category is).
I-trunc : Trunc I l1
I-trunc = tt
