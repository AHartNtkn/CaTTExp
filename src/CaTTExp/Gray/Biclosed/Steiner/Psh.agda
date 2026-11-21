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

------------------------------------------------------------------------
-- Composition of lists of maps, and frames.

infixr 9 _∘ᵐ_
_∘ᵐ_ : ∀ {Ks″ Ks′ Ks} → Maps Ks′ Ks → Maps Ks″ Ks′ → Maps Ks″ Ks
[]       ∘ᵐ []       = []
(a ∷ as) ∘ᵐ (b ∷ bs) = (a ∘M b) ∷ (as ∘ᵐ bs)

_≈ᵐ_ : ∀ {Ks′ Ks} → Maps Ks′ Ks → Maps Ks′ Ks → Set
[]       ≈ᵐ []       = ⊤
(a ∷ as) ≈ᵐ (b ∷ bs) = (a ≈M b) × (as ≈ᵐ bs)

≈ᵐ-refl : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) → hs ≈ᵐ hs
≈ᵐ-refl []       = tt
≈ᵐ-refl (h ∷ hs) = ≈M-refl , ≈ᵐ-refl hs

≈ᵐ-++ : ∀ {A′ A B′ B} {a a′ : Maps A′ A} {b b′ : Maps B′ B} → a ≈ᵐ a′ → b ≈ᵐ b′ → (a ++ᵐ b) ≈ᵐ (a′ ++ᵐ b′)
≈ᵐ-++ {a = []}    {[]}     _        q = q
≈ᵐ-++ {a = _ ∷ _} {_ ∷ _} (p , ps) q = p , ≈ᵐ-++ ps q

⊗s-cong : ∀ {Ks′ Ks} {as bs : Maps Ks′ Ks} → as ≈ᵐ bs → ⊗s as ≈M ⊗s bs
⊗s-cong {as = []}    {[]}     _        = ≈M-refl
⊗s-cong {as = a ∷ as} {b ∷ bs} (p , ps) = ⊗ₘ-cong p (⊗s-cong ps)

⊗s-∘ : ∀ {Ks″ Ks′ Ks} (as : Maps Ks′ Ks) (bs : Maps Ks″ Ks′) → ⊗s (as ∘ᵐ bs) ≈M (⊗s as ∘M ⊗s bs)
⊗s-∘ []       []       = ≈M-sym (∘M-idl (idMap []))
⊗s-∘ (a ∷ as) (b ∷ bs) = ≈M-trans ((a ∘M b) ⊗ₘ (⊗s as ∘M ⊗s bs)) (⊗-congʳ (a ∘M b) (⊗s-∘ as bs)) (⊗ₘ-∘ a b (⊗s as) (⊗s bs))

∘ᵐ-++ : ∀ {A″ A′ A B″ B′ B} (a : Maps A′ A) (b : Maps B′ B) (c : Maps A″ A′) (d : Maps B″ B′) →
        ((a ++ᵐ b) ∘ᵐ (c ++ᵐ d)) ≡ ((a ∘ᵐ c) ++ᵐ (b ∘ᵐ d))
∘ᵐ-++ []       b []       d = refl
∘ᵐ-++ (x ∷ a)  b (y ∷ c)  d = cong ((x ∘M y) ∷_) (∘ᵐ-++ a b c d)

ids-∘ᵐ : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) → (idMaps Ks ∘ᵐ hs) ≈ᵐ hs
ids-∘ᵐ []       = tt
ids-∘ᵐ (h ∷ hs) = ∘M-idl h , ids-∘ᵐ hs

∘ᵐ-ids : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) → (hs ∘ᵐ idMaps Ks′) ≈ᵐ hs
∘ᵐ-ids []       = tt
∘ᵐ-ids (h ∷ hs) = ∘M-idr h , ∘ᵐ-ids hs

idMaps-++ : ∀ A B → idMaps (A ++ B) ≡ (idMaps A ++ᵐ idMaps B)
idMaps-++ []      B = refl
idMaps-++ (K ∷ A) B = cong (idMap K ∷_) (idMaps-++ A B)

⊗s-ids : ∀ Ks → ⊗s (idMaps Ks) ≈M idMap (concat Ks)
⊗s-ids []       = ≈M-refl
⊗s-ids (K ∷ Ks) = ≈M-trans (idMap K ⊗ₘ idMap (concat Ks)) (⊗-congʳ (idMap K) (⊗s-ids Ks)) (⊗ₘ-id K (concat Ks))

castM-∘ʳ : ∀ {K L M M′} (e : M ≡ M′) (g : Map L M) (f : Map K L) → (castM refl e g ∘M f) ≈M castM refl e (g ∘M f)
castM-∘ʳ refl g f = ≈M-refl

-- The frame of a slot: 1_KP ⊗ g ⊗ 1_KQ, flattened.
Fr : ∀ KP KQ {K} Ls → Map K (concat Ls) → Map (concat (KP ++ K ∷ KQ)) (concat (KP ++ Ls ++ KQ))
Fr KP KQ {K} Ls g = castM refl (concat-flat KP Ls KQ) (⊗s (idMaps KP ++ᵐ (g ∷ idMaps KQ)))

Fr-cong : ∀ KP KQ {K} Ls {g g′ : Map K (concat Ls)} → g ≈M g′ → Fr KP KQ Ls g ≈M Fr KP KQ Ls g′
Fr-cong KP KQ Ls e =
  castM-≈M refl (concat-flat KP Ls KQ) (⊗s-cong (≈ᵐ-++ (≈ᵐ-refl (idMaps KP)) (e , ≈ᵐ-refl (idMaps KQ))))

-- a map after the frame
Fr-post : ∀ {KP′ KP KQ′ KQ K Ls Ls₀} (hP : Maps KP′ KP) (hs : Maps Ls Ls₀) (hQ : Maps KQ′ KQ) (g : Map K (concat Ls)) →
          (⊗s (hP ++ᵐ (hs ++ᵐ hQ)) ∘M Fr KP′ KQ′ Ls g)
            ≈M castM refl (concat-flat KP Ls₀ KQ) (⊗s (hP ++ᵐ ((⊗s hs ∘M g) ∷ hQ)))
Fr-post {KP′} {KP} {KQ′} {KQ} {K} {Ls} {Ls₀} hP hs hQ g =
  ≈M-trans (castM (concat-flat KP′ Ls KQ′) (concat-flat KP Ls₀ KQ) N ∘M castM refl (concat-flat KP′ Ls KQ′) M)
           (∘M-cong (≈M-sym (⊗s-flat hP hs hQ)) ≈M-refl)
  (≈M-trans (castM refl (concat-flat KP Ls₀ KQ) (N ∘M M))
            (≈M-sym (castM-∘ refl (concat-flat KP′ Ls KQ′) (concat-flat KP Ls₀ KQ) N M))
            (castM-≈M refl (concat-flat KP Ls₀ KQ)
              (≈M-trans (⊗s ((hP ++ᵐ (⊗s hs ∷ hQ)) ∘ᵐ (idMaps KP′ ++ᵐ (g ∷ idMaps KQ′))))
                        (≈M-sym (⊗s-∘ (hP ++ᵐ (⊗s hs ∷ hQ)) (idMaps KP′ ++ᵐ (g ∷ idMaps KQ′))))
                        (⊗s-cong (subst (λ z → z ≈ᵐ (hP ++ᵐ ((⊗s hs ∘M g) ∷ hQ)))
                                        (sym (∘ᵐ-++ hP (⊗s hs ∷ hQ) (idMaps KP′) (g ∷ idMaps KQ′)))
                                        (≈ᵐ-++ (∘ᵐ-ids hP) (≈M-refl , ∘ᵐ-ids hQ)))))))
  where
    N = ⊗s (hP ++ᵐ (⊗s hs ∷ hQ))
    M = ⊗s (idMaps KP′ ++ᵐ (g ∷ idMaps KQ′))

-- a map before the frame
Fr-pre : ∀ {KP′ KP KQ′ KQ K′ K Ls} (hP : Maps KP′ KP) (h : Map K′ K) (hQ : Maps KQ′ KQ) (g : Map K (concat Ls)) →
         (Fr KP KQ Ls g ∘M ⊗s (hP ++ᵐ (h ∷ hQ)))
           ≈M castM refl (concat-flat KP Ls KQ) (⊗s (hP ++ᵐ ((g ∘M h) ∷ hQ)))
Fr-pre {KP′} {KP} {KQ′} {KQ} {K′} {K} {Ls} hP h hQ g =
  ≈M-trans (castM refl (concat-flat KP Ls KQ) (⊗s (idMaps KP ++ᵐ (g ∷ idMaps KQ)) ∘M ⊗s (hP ++ᵐ (h ∷ hQ))))
           (castM-∘ʳ (concat-flat KP Ls KQ) _ _)
           (castM-≈M refl (concat-flat KP Ls KQ)
             (≈M-trans (⊗s ((idMaps KP ++ᵐ (g ∷ idMaps KQ)) ∘ᵐ (hP ++ᵐ (h ∷ hQ))))
                       (≈M-sym (⊗s-∘ (idMaps KP ++ᵐ (g ∷ idMaps KQ)) (hP ++ᵐ (h ∷ hQ))))
                       (⊗s-cong (subst (λ z → z ≈ᵐ (hP ++ᵐ ((g ∘M h) ∷ hQ)))
                                       (sym (∘ᵐ-++ (idMaps KP) (g ∷ idMaps KQ) hP (h ∷ hQ)))
                                       (≈ᵐ-++ (ids-∘ᵐ hP) (≈M-refl , ids-∘ᵐ hQ))))))
