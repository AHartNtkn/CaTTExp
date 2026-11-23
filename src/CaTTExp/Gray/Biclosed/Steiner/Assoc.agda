------------------------------------------------------------------------
-- The tensor of codes is associative and unital, also on maps (S3).
--
-- Codes compose by ++, which is associative and unital up to ≡
-- (`++-assoc`, `++-[]`). Maps are cast along such equations
-- (`castM`); the casts of (f ⊗ g) ⊗ h and f ⊗ (g ⊗ h) have the same
-- matrix (`⊗-assoc`), and so do f ⊗ id_[] and f (`⊗-unitʳ`). id_[] ⊗ f
-- is f on the nose up to 1 · x = x (`⊗-unitˡ`).
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Assoc (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC)
open import CaTTExp.Gray.Biclosed.Steiner.Tensor nmFB public

++-assoc : ∀ (K L M : Code) → (K ++ L) ++ M ≡ K ++ (L ++ M)
++-assoc []      L M = refl
++-assoc (a ∷ K) L M = cong (a ∷_) (++-assoc K L M)

++-[] : ∀ (K : Code) → K ++ [] ≡ K
++-[] []      = refl
++-[] (a ∷ K) = cong (a ∷_) (++-[] K)

------------------------------------------------------------------------
-- Casts.

castE : ∀ {K K′ : Code} → K ≡ K′ → El K → El K′
castE e = subst El e

castE-cons : ∀ {a} {K K′ : Code} (e : K ≡ K′) i x → castE (cong (a ∷_) e) (i , x) ≡ (i , castE e x)
castE-cons refl i x = refl

castE-inv : ∀ {K K′ : Code} (e : K ≡ K′) x → castE e (castE (sym e) x) ≡ x
castE-inv refl x = refl

castM : ∀ {K K′ L L′} → K ≡ K′ → L ≡ L′ → Map K L → Map K′ L′
castM refl refl m = m

castM-mat : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (m : Map K L) x y →
            mat (castM e₁ e₂ m) (castE e₁ x) (castE e₂ y) ≡ mat m x y
castM-mat refl refl m x y = refl

-- To compare a cast with a map, compare on cast elements.
castM-≈ : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (m : Map K L) (n : Map K′ L′) →
          (∀ x y → mat m x y ≡ mat n (castE e₁ x) (castE e₂ y)) → castM e₁ e₂ m ≈M n
castM-≈ e₁ e₂ m n h = ≈m λ x′ y′ →
  trans (cong₂ (mat (castM e₁ e₂ m)) (sym (castE-inv e₁ x′)) (sym (castE-inv e₂ y′)))
  (trans (castM-mat e₁ e₂ m (castE (sym e₁) x′) (castE (sym e₂) y′))
  (trans (h (castE (sym e₁) x′) (castE (sym e₂) y′))
         (cong₂ (mat n) (castE-inv e₁ x′) (castE-inv e₂ y′))))

castM-cong : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) {m m′ : Map K L} → m ≈M m′ → castM e₁ e₂ m ≈M castM e₁ e₂ m′
castM-cong refl refl e = e

castM-∘ : ∀ {K K′ L L′ M M′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (e₃ : M ≡ M′) (g : Map L M) (f : Map K L) →
          castM e₁ e₃ (g ∘M f) ≈M (castM e₂ e₃ g ∘M castM e₁ e₂ f)
castM-∘ refl refl refl g f = ≈m (λ x y → refl)

castM-id : ∀ {K K′} (e : K ≡ K′) → castM e e (idMap K) ≈M idMap K′
castM-id refl = ≈m (λ x y → refl)

castM-trans : ∀ {K K′ K″ L L′ L″} (e₁ : K ≡ K′) (e₁′ : K′ ≡ K″) (e₂ : L ≡ L′) (e₂′ : L′ ≡ L″) (m : Map K L) →
              castM e₁′ e₂′ (castM e₁ e₂ m) ≈M castM (trans e₁ e₁′) (trans e₂ e₂′) m
castM-trans refl refl refl refl m = ≈m (λ x y → refl)

------------------------------------------------------------------------
-- Joins and casts.

join-assoc : ∀ K L M u v w →
             castE (++-assoc K L M) (join (K ++ L) M (join K L u v) w) ≡ join K (L ++ M) u (join L M v w)
join-assoc []      L M tt      v w = refl
join-assoc (a ∷ K) L M (i , u) v w =
  trans (castE-cons {a = a} (++-assoc K L M) i (join (K ++ L) M (join K L u v) w)) (cong (i ,_) (join-assoc K L M u v w))

join-[] : ∀ K u → castE (++-[] K) (join K [] u tt) ≡ u
join-[] []      tt      = refl
join-[] (a ∷ K) (i , u) = trans (castE-cons {a = a} (++-[] K) i (join K [] u tt)) (cong (i ,_) (join-[] K u))

------------------------------------------------------------------------
-- Associativity and units of ⊗ on maps.

dec3 : ∀ K L M {P : El ((K ++ L) ++ M) → Set} → (∀ u v w → P (join (K ++ L) M (join K L u v) w)) → ∀ x → P x
dec3 K L M {P} h = by-join (K ++ L) M (λ uv w → by-join K L {λ z → P (join (K ++ L) M z w)} (λ u v → h u v w) uv)

⊗-assoc : ∀ {K K′ L L′ M M′} (f : Map K K′) (g : Map L L′) (h : Map M M′) →
          castM (++-assoc K L M) (++-assoc K′ L′ M′) ((f ⊗ₘ g) ⊗ₘ h) ≈M (f ⊗ₘ (g ⊗ₘ h))
⊗-assoc {K} {K′} {L} {L′} {M} {M′} f g h =
  castM-≈ (++-assoc K L M) (++-assoc K′ L′ M′) ((f ⊗ₘ g) ⊗ₘ h) (f ⊗ₘ (g ⊗ₘ h))
    (dec3 K L M λ u v w →
       dec3 K′ L′ M′ {λ y → mat ((f ⊗ₘ g) ⊗ₘ h) (join (K ++ L) M (join K L u v) w) y
                            ≡ mat (f ⊗ₘ (g ⊗ₘ h)) (castE (++-assoc K L M) (join (K ++ L) M (join K L u v) w)) (castE (++-assoc K′ L′ M′) y)}
         λ u′ v′ w′ → go u v w u′ v′ w′)
  where
    go : ∀ u v w u′ v′ w′ →
         mat ((f ⊗ₘ g) ⊗ₘ h) (join (K ++ L) M (join K L u v) w) (join (K′ ++ L′) M′ (join K′ L′ u′ v′) w′)
         ≡ mat (f ⊗ₘ (g ⊗ₘ h)) (castE (++-assoc K L M) (join (K ++ L) M (join K L u v) w))
                               (castE (++-assoc K′ L′ M′) (join (K′ ++ L′) M′ (join K′ L′ u′ v′) w′))
    go u v w u′ v′ w′ =
      trans (tmat-join (f ⊗ₘ g) h (join K L u v) w (join K′ L′ u′ v′) w′)
      (trans (cong (_* mat h w w′) (tmat-join f g u v u′ v′))
      (trans (*-assoc (mat f u u′) (mat g v v′) (mat h w w′))
      (trans (cong (mat f u u′ *_) (sym (tmat-join g h v w v′ w′)))
      (trans (sym (tmat-join f (g ⊗ₘ h) u (join L M v w) u′ (join L′ M′ v′ w′)))
             (sym (cong₂ (mat (f ⊗ₘ (g ⊗ₘ h))) (join-assoc K L M u v w) (join-assoc K′ L′ M′ u′ v′ w′)))))))

⊗-unitʳ : ∀ {K K′} (f : Map K K′) → castM (++-[] K) (++-[] K′) (f ⊗ₘ idMap []) ≈M f
⊗-unitʳ {K} {K′} f =
  castM-≈ (++-[] K) (++-[] K′) (f ⊗ₘ idMap []) f
    (by-join K [] λ u t →
       by-join K′ [] {λ y → mat (f ⊗ₘ idMap []) (join K [] u t) y ≡ mat f (castE (++-[] K) (join K [] u t)) (castE (++-[] K′) y)}
         λ u′ t′ → go u t u′ t′)
  where
    go : ∀ u t u′ t′ → mat (f ⊗ₘ idMap []) (join K [] u t) (join K′ [] u′ t′)
                     ≡ mat f (castE (++-[] K) (join K [] u t)) (castE (++-[] K′) (join K′ [] u′ t′))
    go u tt u′ tt = trans (tmat-join f (idMap []) u tt u′ tt)
                    (trans (*-one (mat f u u′)) (sym (cong₂ (mat f) (join-[] K u) (join-[] K′ u′))))

⊗-unitˡ : ∀ {K K′} (f : Map K K′) → (idMap [] ⊗ₘ f) ≈M f
⊗-unitˡ f = ≈m (λ x y → +-zero (mat f x y))
