------------------------------------------------------------------------
-- Presheaves of setoids on codes, and lists of maps (S4 of the 𝔖̂
-- instance, notes/gray-model-formal-plan.md).
--
-- A presheaf has one carrier U for all codes, a predicate At K x ("x is
-- an element at K"), an equivalence ∼ on all of U, and restriction
-- along maps. Restriction preserves At, ∼ and ≈M, and is functorial on
-- elements that are At. At is invariant under ∼. A single carrier keeps
-- element types independent of codes, so equations between codes (for
-- example concat flattening) never transport elements, only At.
--
-- `Maps Ks′ Ks` is a list of maps Kᵢ′ → Kᵢ and ⊗s their tensor, a map
-- concat Ks′ → concat Ks. Flattening a nested tensor is a cast
-- (`⊗s-++`, `⊗s-flat`).
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Psh (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC)
open import CaTTExp.Gray.Biclosed.Steiner.Assoc nmFB public

record Psh : Set₁ where
  infix 4 _∼_
  field
    U       : Set
    At      : Code → U → Set
    _∼_     : U → U → Set
    ∼-refl  : ∀ {x} → x ∼ x
    ∼-sym   : ∀ {x y} → x ∼ y → y ∼ x
    ∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    res     : ∀ {K L} → Map K L → U → U
    res-cong : ∀ {K L} {f f′ : Map K L} {x x′} → f ≈M f′ → x ∼ x′ → res f x ∼ res f′ x′
    At-res  : ∀ {K L} (f : Map K L) {x} → At L x → At K (res f x)
    At-∼    : ∀ {K x x′} → x ∼ x′ → At K x → At K x′
    res-id  : ∀ {K x} → At K x → res (idMap K) x ∼ x
    res-∘   : ∀ {K L M} (f : Map K L) (g : Map L M) {x} → At M x → res (g ∘M f) x ∼ res f (res g x)
    def     : U

  At-≡ : ∀ {K K′ x} → K ≡ K′ → At K x → At K′ x
  At-≡ refl a = a

  res-cast : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (m : Map K L) x → res (castM e₁ e₂ m) x ≡ res m x
  res-cast refl refl m x = refl

  ∼-≡ : ∀ {x y} → x ≡ y → x ∼ y
  ∼-≡ refl = ∼-refl

open Psh public

------------------------------------------------------------------------
-- Lists of codes and of maps.

concat : List Code → Code
concat []       = []
concat (K ∷ Ks) = K ++ concat Ks

concat-++ : ∀ Ks Ls → concat (Ks ++ Ls) ≡ concat Ks ++ concat Ls
concat-++ []       Ls = refl
concat-++ (K ∷ Ks) Ls = trans (cong (K ++_) (concat-++ Ks Ls)) (sym (++-assoc K (concat Ks) (concat Ls)))

-- flattening one nested slot
concat-flat : ∀ Ps Xs Qs → concat (Ps ++ concat Xs ∷ Qs) ≡ concat (Ps ++ Xs ++ Qs)
concat-flat Ps Xs Qs =
  trans (concat-++ Ps (concat Xs ∷ Qs))
  (trans (cong (concat Ps ++_) (sym (concat-++ Xs Qs)))
         (sym (concat-++ Ps (Xs ++ Qs))))

data Maps : List Code → List Code → Set where
  []  : Maps [] []
  _∷_ : ∀ {K′ K Ks′ Ks} → Map K′ K → Maps Ks′ Ks → Maps (K′ ∷ Ks′) (K ∷ Ks)

⊗s : ∀ {Ks′ Ks} → Maps Ks′ Ks → Map (concat Ks′) (concat Ks)
⊗s []       = idMap []
⊗s (h ∷ hs) = h ⊗ₘ ⊗s hs

_++ᵐ_ : ∀ {Ks′ Ks Ls′ Ls} → Maps Ks′ Ks → Maps Ls′ Ls → Maps (Ks′ ++ Ls′) (Ks ++ Ls)
[]       ++ᵐ gs = gs
(h ∷ hs) ++ᵐ gs = h ∷ (hs ++ᵐ gs)

idMaps : ∀ Ks → Maps Ks Ks
idMaps []       = []
idMaps (K ∷ Ks) = idMap K ∷ idMaps Ks

------------------------------------------------------------------------
-- Casting tensors.

⊗-castʳ : ∀ {K K′ L L′ M M′} (f : Map K K′) (e₁ : L ≡ M) (e₂ : L′ ≡ M′) (g : Map L L′) →
          castM (cong (K ++_) e₁) (cong (K′ ++_) e₂) (f ⊗ₘ g) ≈M (f ⊗ₘ castM e₁ e₂ g)
⊗-castʳ f refl refl g = ≈m (λ x y → refl)

⊗-congʳ : ∀ {K K′ L L′} (f : Map K K′) {g g′ : Map L L′} → g ≈M g′ → (f ⊗ₘ g) ≈M (f ⊗ₘ g′)
⊗-congʳ f {g} {g′} e = ⊗ₘ-cong {f = f} {f′ = f} {g = g} {g′ = g′} (≈m (λ _ _ → refl)) e

≈M-trans : ∀ {K L} {f : Map K L} (g : Map K L) {h : Map K L} → f ≈M g → g ≈M h → f ≈M h
≈M-trans g e e′ = ≈m (λ x y → trans (≈mat e x y) (≈mat e′ x y))

≈M-sym : ∀ {K L} {f g : Map K L} → f ≈M g → g ≈M f
≈M-sym e = ≈m (λ x y → sym (≈mat e x y))

≈M-refl : ∀ {K L} {f : Map K L} → f ≈M f
≈M-refl = ≈m (λ x y → refl)

castM-≈M : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) {m m′ : Map K L} → m ≈M m′ → castM e₁ e₂ m ≈M castM e₁ e₂ m′
castM-≈M refl refl e = e

castM-sym : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) {m : Map K L} {n : Map K′ L′} →
            castM e₁ e₂ m ≈M n → m ≈M castM (sym e₁) (sym e₂) n
castM-sym refl refl e = e

castM-irr : ∀ {K K′ L L′} (e₁ e₁′ : K ≡ K′) (e₂ e₂′ : L ≡ L′) (m : Map K L) → castM e₁ e₂ m ≈M castM e₁′ e₂′ m
castM-irr refl refl refl refl m = ≈m (λ x y → refl)

-- ⊗s (hs ++ gs) is the cast of ⊗s hs ⊗ ⊗s gs.
⊗s-++ : ∀ {Ks′ Ks Ls′ Ls} (hs : Maps Ks′ Ks) (gs : Maps Ls′ Ls) →
        castM (sym (concat-++ Ks′ Ls′)) (sym (concat-++ Ks Ls)) (⊗s hs ⊗ₘ ⊗s gs) ≈M ⊗s (hs ++ᵐ gs)
⊗s-++ [] gs = ⊗-unitˡ (⊗s gs)
⊗s-++ {K′ ∷ Ks′} {K ∷ Ks} {Ls′} {Ls} (h ∷ hs) gs =
  ≈M-trans (castM E₁ E₂ (castM (sym a′) (sym a) (h ⊗ₘ (A ⊗ₘ B)))) (castM-≈M E₁ E₂ step1)
  (≈M-trans (castM (trans (sym a′) E₁) (trans (sym a) E₂) (h ⊗ₘ (A ⊗ₘ B))) (castM-trans (sym a′) E₁ (sym a) E₂ (h ⊗ₘ (A ⊗ₘ B)))
  (≈M-trans (castM (cong (K′ ++_) (sym (concat-++ Ks′ Ls′))) (cong (K ++_) (sym (concat-++ Ks Ls))) (h ⊗ₘ (A ⊗ₘ B)))
            (castM-irr (trans (sym a′) E₁) (cong (K′ ++_) (sym (concat-++ Ks′ Ls′)))
                       (trans (sym a) E₂) (cong (K ++_) (sym (concat-++ Ks Ls))) (h ⊗ₘ (A ⊗ₘ B)))
  (≈M-trans (h ⊗ₘ castM (sym (concat-++ Ks′ Ls′)) (sym (concat-++ Ks Ls)) (A ⊗ₘ B))
            (⊗-castʳ h (sym (concat-++ Ks′ Ls′)) (sym (concat-++ Ks Ls)) (A ⊗ₘ B))
            (⊗-congʳ h (⊗s-++ hs gs)))))
  where
    A = ⊗s hs
    B = ⊗s gs
    a′ = ++-assoc K′ (concat Ks′) (concat Ls′)
    a  = ++-assoc K (concat Ks) (concat Ls)
    E₁ = sym (concat-++ (K′ ∷ Ks′) Ls′)
    E₂ = sym (concat-++ (K ∷ Ks) Ls)
    step1 : ((h ⊗ₘ A) ⊗ₘ B) ≈M castM (sym a′) (sym a) (h ⊗ₘ (A ⊗ₘ B))
    step1 = castM-sym a′ a (⊗-assoc h A B)

-- Flattening one nested slot of a tensor of maps is a cast.
⊗s-flat : ∀ {KP′ KP KX′ KX KQ′ KQ} (hP : Maps KP′ KP) (hX : Maps KX′ KX) (hQ : Maps KQ′ KQ) →
          castM (concat-flat KP′ KX′ KQ′) (concat-flat KP KX KQ) (⊗s (hP ++ᵐ (⊗s hX ∷ hQ))) ≈M ⊗s (hP ++ᵐ (hX ++ᵐ hQ))
⊗s-flat {KP′} {KP} {KX′} {KX} {KQ′} {KQ} hP hX hQ =
  ≈M-trans (castM (concat-flat KP′ KX′ KQ′) (concat-flat KP KX KQ) (castM (sym c1′) (sym c1) G))
           (castM-≈M (concat-flat KP′ KX′ KQ′) (concat-flat KP KX KQ) (≈M-sym (⊗s-++ hP (⊗s hX ∷ hQ))))
  (≈M-trans (castM (trans (sym c1′) (concat-flat KP′ KX′ KQ′)) (trans (sym c1) (concat-flat KP KX KQ)) G)
            (castM-trans (sym c1′) (concat-flat KP′ KX′ KQ′) (sym c1) (concat-flat KP KX KQ) G)
  (≈M-trans (castM (trans (cong (concat KP′ ++_) (sym c2′)) (sym c3′)) (trans (cong (concat KP ++_) (sym c2)) (sym c3)) G)
            (castM-irr _ _ _ _ G)
  (≈M-trans (castM (sym c3′) (sym c3) (castM (cong (concat KP′ ++_) (sym c2′)) (cong (concat KP ++_) (sym c2)) G))
            (≈M-sym (castM-trans (cong (concat KP′ ++_) (sym c2′)) (sym c3′) (cong (concat KP ++_) (sym c2)) (sym c3) G))
  (≈M-trans (castM (sym c3′) (sym c3) (⊗s hP ⊗ₘ castM (sym c2′) (sym c2) (⊗s hX ⊗ₘ ⊗s hQ)))
            (castM-≈M (sym c3′) (sym c3) (⊗-castʳ (⊗s hP) (sym c2′) (sym c2) (⊗s hX ⊗ₘ ⊗s hQ)))
  (≈M-trans (castM (sym c3′) (sym c3) (⊗s hP ⊗ₘ ⊗s (hX ++ᵐ hQ)))
            (castM-≈M (sym c3′) (sym c3) (⊗-congʳ (⊗s hP) (⊗s-++ hX hQ)))
            (⊗s-++ hP (hX ++ᵐ hQ)))))))
  where
    G   = ⊗s hP ⊗ₘ (⊗s hX ⊗ₘ ⊗s hQ)
    c1′ = concat-++ KP′ (concat KX′ ∷ KQ′)
    c1  = concat-++ KP (concat KX ∷ KQ)
    c2′ = concat-++ KX′ KQ′
    c2  = concat-++ KX KQ
    c3′ = concat-++ KP′ (KX′ ++ KQ′)
    c3  = concat-++ KP (KX ++ KQ)
