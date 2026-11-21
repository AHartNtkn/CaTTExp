------------------------------------------------------------------------
-- The formula semantics of the 𝔖̂ instance, and evaluation and
-- currying (S5).
--
-- ⟦obj i⟧ is a parameter presheaf, ⟦rep Θ⟧ = ⟦shp Θ⟧ = y(λΘ), ⊗ is the
-- Day tensor and \\, // are the closures. e^ℓ_{A,C} applies a family
-- φ ∈ (A\C)(K) to an argument at L; curL A C y is the family
-- L, x ↦ y(x, …). The right closure is symmetric, with the argument
-- last.
--
-- curL and curR are total on values: on a value whose profile is not
-- (A, Φ ▸ C), resp. (Φ, A ▸ C), they return the value unchanged.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Sem (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps using (length; take)
open import CaTTExp.Gray.Biclosed.ListLemmas using (drop) renaming (++-assoc to ++-assocL; ++-[] to ++-[]L)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC; globe; named)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB
open import CaTTExp.Gray.Biclosed.Steiner.PshOps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.DayMult nmFB

-- the code of a shape
λS : Shape → Code
λS (disk n)  = globe n ∷ []
λS (named i) = named i ∷ []
λS (Δ ⊠ Θ)   = λS Δ ++ λS Θ

module Sem (ob : Nat → Psh) where

  ⟦_⟧ : Fm → Psh
  ⟦ obj i ⟧  = ob i
  ⟦ rep Θ ⟧  = yP (λS Θ)
  ⟦ shp Θ ⟧  = yP (λS Θ)
  ⟦ A ⊗ B ⟧  = Day ⟦ A ⟧ ⟦ B ⟧
  ⟦ A \\ C ⟧ = LH ⟦ A ⟧ ⟦ C ⟧
  ⟦ C // A ⟧ = RH ⟦ C ⟧ ⟦ A ⟧

  open Interp ⟦_⟧ public

  --------------------------------------------------------------------
  -- General lemmas.

  resL-ids : ∀ As Ks us → AtL As Ks us → resL (idMaps Ks) us ∼L us
  resL-ids []       []       []              _                 = tt
  resL-ids (A ∷ As) (K ∷ Ks) ((.A , x) ∷ us) ((refl , a) , as) = ∼u (res-id ⟦ A ⟧ a) , resL-ids As Ks us as

  res-≈c : ∀ (P : Psh) {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (m : Map K L) (n : Map K′ L′) →
           castM e₁ e₂ m ≈M n → ∀ y → _∼_ P (res P m y) (res P n y)
  res-≈c P e₁ e₂ m n e y = ∼-trans P (∼-≡ P (sym (res-cast P e₁ e₂ m y))) (res-cong P e (∼-refl P))

  -- ⊗s of two maps is their tensor
  cast2 : ∀ {L L′ K K′} (h₁ : Map L′ L) (h₂ : Map K′ K) →
          castM (cong (L′ ++_) (++-[] K′)) (cong (L ++_) (++-[] K)) (⊗s (h₁ ∷ h₂ ∷ [])) ≈M (h₁ ⊗ₘ h₂)
  cast2 {L} {L′} {K} {K′} h₁ h₂ =
    ≈M-trans (h₁ ⊗ₘ castM (++-[] K′) (++-[] K) (h₂ ⊗ₘ idMap [])) (⊗-castʳ h₁ (++-[] K′) (++-[] K) (h₂ ⊗ₘ idMap []))
             (⊗-congʳ h₁ (⊗-unitʳ h₂))

  record Cons (A : Fm) (As : List Fm) (Ks : List Code) (us : List Uni) : Set where
    constructor cns
    field
      K₀  : Code
      Ks′ : List Code
      x₀  : UF A
      us′ : List Uni
      eK  : Ks ≡ K₀ ∷ Ks′
      eU  : us ≡ (A , x₀) ∷ us′
      a₀  : At ⟦ A ⟧ K₀ x₀
      as  : AtL As Ks′ us′

  AtL-cons : ∀ {A As Ks us} → AtL (A ∷ As) Ks us → Cons A As Ks us
  AtL-cons {A} {As} {K ∷ Ks} {(.A , x) ∷ us} ((refl , a) , as) = cns K Ks x us refl refl a as

  infixr 5 _⟨_⟩_
  _⟨_⟩_ : ∀ (P : Psh) {x y z : U P} → _∼_ P x y → _∼_ P y z → _∼_ P x z
  _⟨_⟩_ P = ∼-trans P

  --------------------------------------------------------------------
  -- Evaluation.

  evLraw : ∀ A C → List Code → List Uni → UF C
  evLraw A C (L ∷ Ks) (u ∷ w ∷ us) = co (A \\ C) w L (co A u)
  evLraw A C []       us           = def ⟦ C ⟧
  evLraw A C (L ∷ Ks) []           = def ⟦ C ⟧
  evLraw A C (L ∷ Ks) (u ∷ [])     = def ⟦ C ⟧

  evL-val : ∀ A C L Ks x φ us → evLraw A C (L ∷ Ks) ((A , x) ∷ (A \\ C , φ) ∷ us) ≡ φ L x
  evL-val A C L Ks x φ us = cong₂ (λ f y → f L y) (co-id (A \\ C) φ) (co-id A x)

  evLok : ∀ A C → Ok ((A ∷ (A \\ C) ∷ []) ▸ C) (evLraw A C)
  evLok A C = ok at cg nt
    where
      Cp = ⟦ C ⟧
      at : ∀ Ks us → AtL (A ∷ (A \\ C) ∷ []) Ks us → At Cp (concat Ks) (evLraw A C Ks us)
      at Ks us a with AtL-cons a
      ... | cns L _ x _ refl refl ax as with AtL-cons as
      ...   | cns K _ φ _ refl refl aφ as′ with AtL-nil as′
      ...     | refl , refl =
        subst (At Cp (L ++ (K ++ []))) (sym (evL-val A C L (K ∷ []) x φ []))
              (At-≡ Cp (cong (L ++_) (sym (++-[] K))) (fat aφ L x ax))
      cg : ∀ Ks us vs → AtL (A ∷ (A \\ C) ∷ []) Ks us → AtL (A ∷ (A \\ C) ∷ []) Ks vs → us ∼L vs →
           _∼_ Cp (evLraw A C Ks us) (evLraw A C Ks vs)
      cg Ks us vs a b e with AtL-cons a | AtL-cons b
      ... | cns L _ x _ refl refl ax as | cns _ _ x′ _ refl refl ax′ bs with AtL-cons as | AtL-cons bs | e
      ...   | cns K _ φ _ refl refl aφ _ | cns _ _ φ′ _ refl refl _ _ | ∼u ex , ∼u eφ , _ =
        Cp ⟨ ∼-≡ Cp (evL-val A C L (K ∷ []) x φ []) ⟩
        Cp ⟨ fcg aφ L x x′ ax ax′ ex ⟩
        Cp ⟨ eφ L x′ ax′ ⟩ ∼-≡ Cp (sym (evL-val A C L (K ∷ []) x′ φ′ []))
      nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL (A ∷ (A \\ C) ∷ []) Ks us →
           _∼_ Cp (evLraw A C Ks′ (resL hs us)) (res Cp (⊗s hs) (evLraw A C Ks us))
      nt hs us a with AtL-cons a
      ... | cns L _ x _ refl refl ax as with AtL-cons as
      ...   | cns K _ φ _ refl refl aφ as′ with AtL-nil as′
      nt {L′ ∷ K′ ∷ []} (h₁ ∷ h₂ ∷ []) _ _ | cns L _ x _ refl refl ax as | cns K _ φ _ refl refl aφ as′ | refl , refl =
        Cp ⟨ ∼-≡ Cp (evL-val A C L′ (K′ ∷ []) (res ⟦ A ⟧ h₁ x) (resLH ⟦ A ⟧ Cp h₂ φ) []) ⟩
        Cp ⟨ res-cong Cp ≈M-refl (fnat aφ h₁ x ax) ⟩
        Cp ⟨ ∼-sym Cp (res-∘ Cp (idMap L′ ⊗ₘ h₂) (h₁ ⊗ₘ idMap K) (fat aφ L x ax)) ⟩
        Cp ⟨ res-cong Cp (⊗-split₁ h₁ h₂) (∼-refl Cp) ⟩
        Cp ⟨ ∼-sym Cp (res-≈c Cp _ _ (⊗s (h₁ ∷ h₂ ∷ [])) (h₁ ⊗ₘ h₂) (cast2 h₁ h₂) (φ L x)) ⟩
             ∼-≡ Cp (cong (res Cp (⊗s (h₁ ∷ h₂ ∷ []))) (sym (evL-val A C L (K ∷ []) x φ [])))

  evL : Fm → Fm → Val
  evL A C = mk ((A ∷ (A \\ C) ∷ []) ▸ C) (evLraw A C) (evLok A C)

  evRraw : ∀ A C → List Code → List Uni → UF C
  evRraw A C (K ∷ L ∷ Ks) (w ∷ u ∷ us) = co (C // A) w L (co A u)
  evRraw A C []           us           = def ⟦ C ⟧
  evRraw A C (K ∷ [])     us           = def ⟦ C ⟧
  evRraw A C (K ∷ L ∷ Ks) []           = def ⟦ C ⟧
  evRraw A C (K ∷ L ∷ Ks) (w ∷ [])     = def ⟦ C ⟧

  evR-val : ∀ A C K L Ks φ x us → evRraw A C (K ∷ L ∷ Ks) ((C // A , φ) ∷ (A , x) ∷ us) ≡ φ L x
  evR-val A C K L Ks φ x us = cong₂ (λ f y → f L y) (co-id (C // A) φ) (co-id A x)

  evRok : ∀ A C → Ok (((C // A) ∷ A ∷ []) ▸ C) (evRraw A C)
  evRok A C = ok at cg nt
    where
      Cp = ⟦ C ⟧
      at : ∀ Ks us → AtL ((C // A) ∷ A ∷ []) Ks us → At Cp (concat Ks) (evRraw A C Ks us)
      at Ks us a with AtL-cons a
      ... | cns K _ φ _ refl refl aφ as with AtL-cons as
      ...   | cns L _ x _ refl refl ax as′ with AtL-nil as′
      ...     | refl , refl =
        subst (At Cp (K ++ (L ++ []))) (sym (evR-val A C K L [] φ x []))
              (At-≡ Cp (cong (K ++_) (sym (++-[] L))) (gat aφ L x ax))
      cg : ∀ Ks us vs → AtL ((C // A) ∷ A ∷ []) Ks us → AtL ((C // A) ∷ A ∷ []) Ks vs → us ∼L vs →
           _∼_ Cp (evRraw A C Ks us) (evRraw A C Ks vs)
      cg Ks us vs a b e with AtL-cons a | AtL-cons b
      ... | cns K _ φ _ refl refl aφ as | cns _ _ φ′ _ refl refl _ bs with AtL-cons as | AtL-cons bs | e
      ...   | cns L _ x _ refl refl ax _ | cns _ _ x′ _ refl refl ax′ _ | ∼u eφ , ∼u ex , _ =
        Cp ⟨ ∼-≡ Cp (evR-val A C K L [] φ x []) ⟩
        Cp ⟨ gcg aφ L x x′ ax ax′ ex ⟩
        Cp ⟨ eφ L x′ ax′ ⟩ ∼-≡ Cp (sym (evR-val A C K L [] φ′ x′ []))
      nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL ((C // A) ∷ A ∷ []) Ks us →
           _∼_ Cp (evRraw A C Ks′ (resL hs us)) (res Cp (⊗s hs) (evRraw A C Ks us))
      nt hs us a with AtL-cons a
      ... | cns K _ φ _ refl refl aφ as with AtL-cons as
      ...   | cns L _ x _ refl refl ax as′ with AtL-nil as′
      nt {K′ ∷ L′ ∷ []} (h₁ ∷ h₂ ∷ []) _ _ | cns K _ φ _ refl refl aφ as | cns L _ x _ refl refl ax as′ | refl , refl =
        Cp ⟨ ∼-≡ Cp (evR-val A C K′ L′ [] (resRH Cp ⟦ A ⟧ h₁ φ) (res ⟦ A ⟧ h₂ x) []) ⟩
        Cp ⟨ res-cong Cp ≈M-refl (gnat aφ h₂ x ax) ⟩
        Cp ⟨ ∼-sym Cp (res-∘ Cp (h₁ ⊗ₘ idMap L′) (idMap K ⊗ₘ h₂) (gat aφ L x ax)) ⟩
        Cp ⟨ res-cong Cp (⊗-split₂ h₁ h₂) (∼-refl Cp) ⟩
        Cp ⟨ ∼-sym Cp (res-≈c Cp _ _ (⊗s (h₁ ∷ h₂ ∷ [])) (h₁ ⊗ₘ h₂) (cast2 h₁ h₂) (φ L x)) ⟩
             ∼-≡ Cp (cong (res Cp (⊗s (h₁ ∷ h₂ ∷ []))) (sym (evR-val A C K L [] φ x [])))

  evR : Fm → Fm → Val
  evR A C = mk (((C // A) ∷ A ∷ []) ▸ C) (evRraw A C) (evRok A C)

  --------------------------------------------------------------------
  -- Left currying.

  clraw : ∀ A C → (List Code → List Uni → UF C) → List Code → List Uni → UF (A \\ C)
  clraw A C r Ks us L x = r (L ∷ Ks) ((A , x) ∷ us)

  clok : ∀ {A Φ C} {r : List Code → List Uni → UF C} → Ok ((A ∷ Φ) ▸ C) r → Ok (Φ ▸ (A \\ C)) (clraw A C r)
  clok {A} {Φ} {C} {r} o = ok at cg nt
    where
      Cp = ⟦ C ⟧
      at : ∀ Ks us → AtL Φ Ks us → At ⟦ A \\ C ⟧ (concat Ks) (clraw A C r Ks us)
      at Ks us a = atlh
        (λ L x ax → vAt o (L ∷ Ks) ((A , x) ∷ us) ((refl , ax) , a))
        (λ L x x′ ax ax′ e → vcong o (L ∷ Ks) _ _ ((refl , ax) , a) ((refl , ax′) , a) (∼u e , ∼L-refl us))
        (λ {L′} {L} h x ax →
           Cp ⟨ vcong o (L′ ∷ Ks) ((A , res ⟦ A ⟧ h x) ∷ us) ((A , res ⟦ A ⟧ h x) ∷ resL (idMaps Ks) us)
                      ((refl , At-res ⟦ A ⟧ h ax) , a) ((refl , At-res ⟦ A ⟧ h ax) , AtL-res Φ (idMaps Ks) us a)
                      (∼U-refl , ∼L-sym′ (resL-ids Φ Ks us a)) ⟩
           Cp ⟨ vnat o (h ∷ idMaps Ks) ((A , x) ∷ us) ((refl , ax) , a) ⟩
                res-cong Cp (⊗-congʳ h (⊗s-ids Ks)) (∼-refl Cp))
        where
          ∼L-sym′ : ∀ {as bs} → as ∼L bs → bs ∼L as
          ∼L-sym′ {[]} {[]} _ = tt
          ∼L-sym′ {a ∷ as} {b ∷ bs} (p , ps) = ∼U-sym p , ∼L-sym′ ps
      cg : ∀ Ks us vs → AtL Φ Ks us → AtL Φ Ks vs → us ∼L vs → _∼_ ⟦ A \\ C ⟧ (clraw A C r Ks us) (clraw A C r Ks vs)
      cg Ks us vs a b e L x ax = vcong o (L ∷ Ks) _ _ ((refl , ax) , a) ((refl , ax) , b) (∼U-refl , e)
      nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL Φ Ks us →
           _∼_ ⟦ A \\ C ⟧ (clraw A C r Ks′ (resL hs us)) (res ⟦ A \\ C ⟧ (⊗s hs) (clraw A C r Ks us))
      nt {Ks′} {Ks} hs us a L x ax =
        Cp ⟨ vcong o (L ∷ Ks′) ((A , x) ∷ resL hs us) ((A , res ⟦ A ⟧ (idMap L) x) ∷ resL hs us)
                   ((refl , ax) , AtL-res Φ hs us a) ((refl , At-res ⟦ A ⟧ (idMap L) ax) , AtL-res Φ hs us a)
                   (∼u (∼-sym ⟦ A ⟧ (res-id ⟦ A ⟧ ax)) , ∼L-refl (resL hs us)) ⟩
             vnat o (idMap L ∷ hs) ((A , x) ∷ us) ((refl , ax) , a)

  curL-at : ∀ A C {B Φ C′} (r : List Code → List Uni → UF C′) → Ok ((B ∷ Φ) ▸ C′) r → Maybe (B ≡ A) → Maybe (C′ ≡ C) → Val
  curL-at A C {Φ = Φ} r o (just refl) (just refl) = mk (Φ ▸ (A \\ C)) (clraw A C r) (clok o)
  curL-at A C {B} {Φ} {C′} r o _ _ = mk ((B ∷ Φ) ▸ C′) r o

  curL : Fm → Fm → Val → Val
  curL A C (mk ((B ∷ Φ) ▸ C′) r o) = curL-at A C r o (decFm B A) (decFm C′ C)
  curL A C (mk ([] ▸ C′) r o)      = mk ([] ▸ C′) r o

  curL-ok : ∀ {A Φ C} (r : List Code → List Uni → UF C) (o : Ok ((A ∷ Φ) ▸ C) r) →
            curL A C (mk ((A ∷ Φ) ▸ C) r o) ≡ mk (Φ ▸ (A \\ C)) (clraw A C r) (clok o)
  curL-ok {A} {Φ} {C} r o = cong₂ (curL-at A C r o) (decFm-refl A) (decFm-refl C)

  T-curL : ∀ {y A Φ C} → y ∶ ((A ∷ Φ) ▸ C) → curL A C y ∶ (Φ ▸ (A \\ C))
  T-curL {mk _ r o} refl = cong prof (curL-ok r o)

  curL-cong : ∀ {y y′} A C → y ≈ y′ → curL A C y ≈ curL A C y′
  curL-cong A C (≈c {[] ▸ C′} e) = ≈c e
  curL-cong A C (≈c {(B ∷ Φ) ▸ C′} {r} {r′} {o} {o′} e) = go (decFm B A) (decFm C′ C)
    where go : (m₁ : Maybe (B ≡ A)) (m₂ : Maybe (C′ ≡ C)) → curL-at A C r o m₁ m₂ ≈ curL-at A C r′ o′ m₁ m₂
          go (just refl) (just refl) = ≈c (λ Ks us a L x ax → e (L ∷ Ks) ((A , x) ∷ us) ((refl , ax) , a))
          go (just refl) nothing     = ≈c e
          go nothing     m₂          = ≈c e

  private
    sL : ∀ A C → Slot (A ∷ (A \\ C) ∷ []) 1 (A \\ C)
    sL A C = slot (A ∷ []) [] refl refl

  curL-l : ∀ {x A Φ C} → x ∶ (Φ ▸ (A \\ C)) → curL A C (pc (evL A C) 1 x) ≈ x
  curL-l {mk _ r o} {A} {Φ} {C} refl =
    ≈-trans (≈-≡ (trans (cong (curL A C) (pc-just (evLok A C) o 1 (sL A C)))
                        (curL-ok (PC.rc (evLok A C) o 1 (sL A C)) (PC.cok (evLok A C) o 1 (sL A C)))))
            (≈-ins (++-[]L Φ) H)
    where
      rc = PC.rc (evLok A C) o 1 (sL A C)
      H : ∀ Ks us → AtL (Φ ++ []) Ks us → _∼_ ⟦ A \\ C ⟧ (clraw A C rc Ks us) (r Ks us)
      H Ks us a L x ax = ∼-≡ ⟦ C ⟧
        (trans (cong₂ rc (cong (L ∷_) (sym (++-[]L Ks))) (cong ((A , x) ∷_) (sym (++-[]L us))))
        (trans (PC.evA (evLok A C) o 1 (sL A C) {KQ = []} {uQ = []} ((refl , ax) , tt)
                 (subst (λ Is → AtL Is Ks us) (++-[]L Φ) a))
               (evL-val A C L (concat Ks ∷ []) x (r Ks us) [])))

  curL-r : ∀ {y A Φ C} → y ∶ ((A ∷ Φ) ▸ C) → pc (evL A C) 1 (curL A C y) ≈ y
  curL-r {mk _ r o} {A} {Φ} {C} refl =
    ≈-trans (≈-≡ (trans (cong (pc (evL A C) 1) (curL-ok r o)) (pc-just (evLok A C) (clok o) 1 (sL A C))))
            (≈-ins (cong (A ∷_) (++-[]L Φ)) H)
    where
      rc = PC.rc (evLok A C) (clok o) 1 (sL A C)
      H : ∀ Ks us → AtL (A ∷ (Φ ++ [])) Ks us → _∼_ ⟦ C ⟧ (rc Ks us) (r Ks us)
      H Ks us a with AtL-cons a
      ... | cns L Ks′ x us′ refl refl ax as = ∼-≡ ⟦ C ⟧
        (trans (cong₂ rc (cong (L ∷_) (sym (++-[]L Ks′))) (cong ((A , x) ∷_) (sym (++-[]L us′))))
        (trans (PC.evA (evLok A C) (clok o) 1 (sL A C) {KQ = []} {uQ = []} ((refl , ax) , tt)
                 (subst (λ Is → AtL Is Ks′ us′) (++-[]L Φ) as))
               (evL-val A C L (concat Ks′ ∷ []) x (clraw A C r Ks′ us′) [])))

  --------------------------------------------------------------------
  -- Right currying.

  Snoc : List Fm → Set
  Snoc Is = Σ (List Fm × Fm) (λ p → Is ≡ fst p ++ snd p ∷ [])

  unsnoc : (Is : List Fm) → Maybe (Snoc Is)
  unsnoc []           = nothing
  unsnoc (F ∷ [])     = just (([] , F) , refl)
  unsnoc (F ∷ G ∷ Fs) with unsnoc (G ∷ Fs)
  ... | nothing                = nothing
  ... | just ((Φ , B) , e)     = just ((F ∷ Φ , B) , cong (F ∷_) e)

  unsnoc-ok : ∀ Φ A → unsnoc (Φ ++ A ∷ []) ≡ just ((Φ , A) , refl)
  unsnoc-ok []           A = refl
  unsnoc-ok (F ∷ [])     A = refl
  unsnoc-ok (F ∷ G ∷ Φ)  A rewrite unsnoc-ok (G ∷ Φ) A = refl

  concat-snoc : ∀ Ks L → concat (Ks ++ L ∷ []) ≡ concat Ks ++ L
  concat-snoc Ks L = trans (concat-++ Ks (L ∷ [])) (cong (concat Ks ++_) (++-[] L))

  crraw : ∀ A C → (List Code → List Uni → UF C) → List Code → List Uni → UF (C // A)
  crraw A C r Ks us L x = r (Ks ++ L ∷ []) (us ++ (A , x) ∷ [])

  private
    ∼L-sym′ : ∀ {as bs} → as ∼L bs → bs ∼L as
    ∼L-sym′ {[]} {[]} _ = tt
    ∼L-sym′ {a ∷ as} {b ∷ bs} (p , ps) = ∼U-sym p , ∼L-sym′ ps

    AtL-snoc : ∀ {Φ A Ks us L x} → AtL Φ Ks us → At ⟦ A ⟧ L x → AtL (Φ ++ A ∷ []) (Ks ++ L ∷ []) (us ++ (A , x) ∷ [])
    AtL-snoc {Φ} {A} {Ks} {us} {L} a ax = AtL-++ {Φ} {A ∷ []} {Ks} {L ∷ []} {us} a ((refl , ax) , tt)

    lenU : ∀ {Φ Ks us} → AtL Φ Ks us → length us ≡ length Ks
    lenU {Φ} {Ks} {us} a = trans (AtL-lenU Φ Ks us a) (sym (AtL-lenK Φ Ks us a))

    -- ⊗s (1 ⊗ … ⊗ 1, h) and ⊗s (hs, 1) as tensors of two maps
    ⊗s-snoc : ∀ {Ks′ Ks L′ L} (hs : Maps Ks′ Ks) (h : Map L′ L) →
              castM (concat-snoc Ks′ L′) (concat-snoc Ks L) (⊗s (hs ++ᵐ (h ∷ []))) ≈M (⊗s hs ⊗ₘ h)
    ⊗s-snoc {Ks′} {Ks} {L′} {L} hs h =
      ≈M-trans (castM (trans (concat-++ Ks′ (L′ ∷ [])) (cong (concat Ks′ ++_) (++-[] L′)))
                      (trans (concat-++ Ks (L ∷ [])) (cong (concat Ks ++_) (++-[] L)))
                      (castM (sym (concat-++ Ks′ (L′ ∷ []))) (sym (concat-++ Ks (L ∷ []))) (⊗s hs ⊗ₘ ⊗s (h ∷ []))))
               (castM-≈M _ _ (≈M-sym (⊗s-++ hs (h ∷ []))))
      (≈M-trans (castM (trans (sym (concat-++ Ks′ (L′ ∷ []))) (trans (concat-++ Ks′ (L′ ∷ [])) (cong (concat Ks′ ++_) (++-[] L′))))
                       (trans (sym (concat-++ Ks (L ∷ []))) (trans (concat-++ Ks (L ∷ [])) (cong (concat Ks ++_) (++-[] L))))
                       (⊗s hs ⊗ₘ ⊗s (h ∷ [])))
                (castM-trans (sym (concat-++ Ks′ (L′ ∷ []))) (concat-snoc Ks′ L′) (sym (concat-++ Ks (L ∷ []))) (concat-snoc Ks L) (⊗s hs ⊗ₘ ⊗s (h ∷ [])))
      (≈M-trans (castM (cong (concat Ks′ ++_) (++-[] L′)) (cong (concat Ks ++_) (++-[] L)) (⊗s hs ⊗ₘ (h ⊗ₘ idMap [])))
                (castM-irr _ _ _ _ (⊗s hs ⊗ₘ (h ⊗ₘ idMap [])))
      (≈M-trans (⊗s hs ⊗ₘ castM (++-[] L′) (++-[] L) (h ⊗ₘ idMap []))
                (⊗-castʳ (⊗s hs) (++-[] L′) (++-[] L) (h ⊗ₘ idMap []))
                (⊗-congʳ (⊗s hs) (⊗-unitʳ h)))))

  crok : ∀ {A Φ C} {r : List Code → List Uni → UF C} → Ok ((Φ ++ A ∷ []) ▸ C) r → Ok (Φ ▸ (C // A)) (crraw A C r)
  crok {A} {Φ} {C} {r} o = ok at cg nt
    where
      Cp = ⟦ C ⟧
      at : ∀ Ks us → AtL Φ Ks us → At ⟦ C // A ⟧ (concat Ks) (crraw A C r Ks us)
      at Ks us a = atrh
        (λ L x ax → At-≡ Cp (concat-snoc Ks L) (vAt o (Ks ++ L ∷ []) (us ++ (A , x) ∷ []) (AtL-snoc a ax)))
        (λ L x x′ ax ax′ e → vcong o (Ks ++ L ∷ []) _ _ (AtL-snoc a ax) (AtL-snoc a ax′)
                                   (∼L-++ {us} {us} (∼L-refl us) (∼u e , tt)))
        (λ {L′} {L} h x ax →
           Cp ⟨ vcong o (Ks ++ L′ ∷ []) (us ++ (A , res ⟦ A ⟧ h x) ∷ []) (resL (idMaps Ks ++ᵐ (h ∷ [])) (us ++ (A , x) ∷ []))
                      (AtL-snoc a (At-res ⟦ A ⟧ h ax)) (AtL-res (Φ ++ A ∷ []) (idMaps Ks ++ᵐ (h ∷ [])) _ (AtL-snoc a ax))
                      (subst (λ vs → (us ++ (A , res ⟦ A ⟧ h x) ∷ []) ∼L vs)
                             (sym (resL-++ (idMaps Ks) (h ∷ []) us ((A , x) ∷ []) (lenU a)))
                             (∼L-++ {us} {resL (idMaps Ks) us} (∼L-sym′ (resL-ids Φ Ks us a)) (∼U-refl , tt))) ⟩
           Cp ⟨ vnat o (idMaps Ks ++ᵐ (h ∷ [])) (us ++ (A , x) ∷ []) (AtL-snoc a ax) ⟩
           Cp ⟨ res-≈c Cp (concat-snoc Ks L′) (concat-snoc Ks L) (⊗s (idMaps Ks ++ᵐ (h ∷ []))) (⊗s (idMaps Ks) ⊗ₘ h)
                       (⊗s-snoc (idMaps Ks) h) _ ⟩
                res-cong Cp (⊗ₘ-cong (⊗s-ids Ks) ≈M-refl) (∼-refl Cp))
      cg : ∀ Ks us vs → AtL Φ Ks us → AtL Φ Ks vs → us ∼L vs → _∼_ ⟦ C // A ⟧ (crraw A C r Ks us) (crraw A C r Ks vs)
      cg Ks us vs a b e L x ax = vcong o (Ks ++ L ∷ []) _ _ (AtL-snoc a ax) (AtL-snoc b ax) (∼L-++ {us} {vs} e (∼U-refl , tt))
      nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL Φ Ks us →
           _∼_ ⟦ C // A ⟧ (crraw A C r Ks′ (resL hs us)) (res ⟦ C // A ⟧ (⊗s hs) (crraw A C r Ks us))
      nt {Ks′} {Ks} hs us a L x ax =
        Cp ⟨ vcong o (Ks′ ++ L ∷ []) (resL hs us ++ (A , x) ∷ []) (resL (hs ++ᵐ (idMap L ∷ [])) (us ++ (A , x) ∷ []))
                   (AtL-snoc (AtL-res Φ hs us a) ax) (AtL-res (Φ ++ A ∷ []) (hs ++ᵐ (idMap L ∷ [])) _ (AtL-snoc a ax))
                   (subst (λ vs → (resL hs us ++ (A , x) ∷ []) ∼L vs)
                          (sym (resL-++ hs (idMap L ∷ []) us ((A , x) ∷ []) (lenU a)))
                          (∼L-++ {resL hs us} {resL hs us} (∼L-refl (resL hs us))
                                 (∼u (∼-sym ⟦ A ⟧ (res-id ⟦ A ⟧ ax)) , tt))) ⟩
        Cp ⟨ vnat o (hs ++ᵐ (idMap L ∷ [])) (us ++ (A , x) ∷ []) (AtL-snoc a ax) ⟩
             res-≈c Cp (concat-snoc Ks′ L) (concat-snoc Ks L) (⊗s (hs ++ᵐ (idMap L ∷ []))) (⊗s hs ⊗ₘ idMap L)
                    (⊗s-snoc hs (idMap L)) _

  curR-at2 : ∀ A C {B Φ} (r : List Code → List Uni → UF C) → Ok ((Φ ++ B ∷ []) ▸ C) r → Maybe (B ≡ A) → Val
  curR-at2 A C {Φ = Φ} r o (just refl) = mk (Φ ▸ (C // A)) (crraw A C r) (crok o)
  curR-at2 A C {B} {Φ} r o nothing     = mk ((Φ ++ B ∷ []) ▸ C) r o

  curR-at : ∀ A C {Is C′} (r : List Code → List Uni → UF C′) → Ok (Is ▸ C′) r → Maybe (Snoc Is) → Maybe (C′ ≡ C) → Val
  curR-at A C r o (just ((Φ , B) , refl)) (just refl) = curR-at2 A C r o (decFm B A)
  curR-at A C {Is} {C′} r o _ _ = mk (Is ▸ C′) r o

  curR : Fm → Fm → Val → Val
  curR A C (mk (Is ▸ C′) r o) = curR-at A C r o (unsnoc Is) (decFm C′ C)

  curR-ok : ∀ {A Φ C} (r : List Code → List Uni → UF C) (o : Ok ((Φ ++ A ∷ []) ▸ C) r) →
            curR A C (mk ((Φ ++ A ∷ []) ▸ C) r o) ≡ mk (Φ ▸ (C // A)) (crraw A C r) (crok o)
  curR-ok {A} {Φ} {C} r o rewrite unsnoc-ok Φ A | decFm-refl C | decFm-refl A = refl

  T-curR : ∀ {y A Φ C} → y ∶ ((Φ ++ A ∷ []) ▸ C) → curR A C y ∶ (Φ ▸ (C // A))
  T-curR {mk _ r o} refl = cong prof (curR-ok r o)

  curR-cong : ∀ {y y′} A C → y ≈ y′ → curR A C y ≈ curR A C y′
  curR-cong A C (≈c {Is ▸ C′} {r} {r′} {o} {o′} e) = go (unsnoc Is) (decFm C′ C)
    where
      go2 : ∀ {B Φ} {r r′ : List Code → List Uni → UF C} {o : Ok ((Φ ++ B ∷ []) ▸ C) r} {o′ : Ok ((Φ ++ B ∷ []) ▸ C) r′} →
            (∀ Ks us → AtL (Φ ++ B ∷ []) Ks us → _∼_ ⟦ C ⟧ (r Ks us) (r′ Ks us)) →
            (m : Maybe (B ≡ A)) → curR-at2 A C r o m ≈ curR-at2 A C r′ o′ m
      go2 e (just refl) = ≈c (λ Ks us a L x ax → e (Ks ++ L ∷ []) (us ++ (A , x) ∷ []) (AtL-snoc a ax))
      go2 e nothing     = ≈c e
      go : (m₁ : Maybe (Snoc Is)) (m₂ : Maybe (C′ ≡ C)) → curR-at A C r o m₁ m₂ ≈ curR-at A C r′ o′ m₁ m₂
      go (just ((Φ , B) , refl)) (just refl) = go2 e (decFm B A)
      go (just ((Φ , B) , refl)) nothing     = ≈c e
      go nothing                 m₂          = ≈c e

  private
    sR : ∀ A C → Slot ((C // A) ∷ A ∷ []) 0 (C // A)
    sR A C = slot [] (A ∷ []) refl refl

  curR-l : ∀ {x A Φ C} → x ∶ (Φ ▸ (C // A)) → curR A C (pc (evR A C) 0 x) ≈ x
  curR-l {mk _ r o} {A} {Φ} {C} refl =
    ≈-trans (≈-≡ (trans (cong (curR A C) (pc-just (evRok A C) o 0 (sR A C)))
                        (curR-ok (PC.rc (evRok A C) o 0 (sR A C)) (PC.cok (evRok A C) o 0 (sR A C)))))
            (≈c H)
    where
      rc = PC.rc (evRok A C) o 0 (sR A C)
      H : ∀ Ks us → AtL Φ Ks us → _∼_ ⟦ C // A ⟧ (crraw A C rc Ks us) (r Ks us)
      H Ks us a L x ax = ∼-≡ ⟦ C ⟧
        (trans (PC.evA (evRok A C) o 0 (sR A C) {KQ = L ∷ []} {uQ = (A , x) ∷ []} tt a)
               (evR-val A C (concat Ks) L [] (r Ks us) x []))

  curR-r : ∀ {y A Φ C} → y ∶ ((Φ ++ A ∷ []) ▸ C) → pc (evR A C) 0 (curR A C y) ≈ y
  curR-r {mk _ r o} {A} {Φ} {C} refl =
    ≈-trans (≈-≡ (trans (cong (pc (evR A C) 0) (curR-ok r o)) (pc-just (evRok A C) (crok o) 0 (sR A C))))
            (≈c H)
    where
      rc = PC.rc (evRok A C) (crok o) 0 (sR A C)
      H : ∀ Ks us → AtL (Φ ++ A ∷ []) Ks us → _∼_ ⟦ C ⟧ (rc Ks us) (r Ks us)
      H Ks us a with AtL-split Φ (A ∷ []) Ks us a
      ... | sp KΦ K₂ uΦ u₂ refl refl aΦ a₂ with AtL-cons a₂
      ...   | cns L _ x _ refl refl ax as with AtL-nil as
      ...     | refl , refl = ∼-≡ ⟦ C ⟧
        (trans (PC.evA (evRok A C) (crok o) 0 (sR A C) {KQ = L ∷ []} {uQ = (A , x) ∷ []} tt aΦ)
               (evR-val A C (concat KΦ) L [] (crraw A C r KΦ uΦ) x []))

  T-evL : ∀ A C → evL A C ∶ ((A ∷ (A \\ C) ∷ []) ▸ C)
  T-evL A C = refl

  T-evR : ∀ A C → evR A C ∶ (((C // A) ∷ A ∷ []) ▸ C)
  T-evR A C = refl
