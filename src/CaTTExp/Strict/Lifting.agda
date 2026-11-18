------------------------------------------------------------------------
-- Toward unique lifting (ledger A5, existence half of N2), step L2.
--
-- A cell of ν(K) is determined by its r-source and its rows above r:
-- row r⁺ is forced by the boundary condition and cancellation (or, at
-- the top, by x⁻ = x⁺). Consequently the factors of y #ᵣ z are
-- determined by the composite and by their rows above r (the converse
-- of the cut lemma; fixed-list uniqueness, outside response §1.2).
------------------------------------------------------------------------
module CaTTExp.Strict.Lifting where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu

module Det (K : ADC) (L : Nat) where
  open ADC K

  private
    Tb = Tab 𝕄

  -- Rows strictly above r agree.
  Above : ∀ {m} → Nat → Tb m → Tb m → Set
  Above n       []      []        = ⊤
  Above zero    (e ∷ r) (e′ ∷ r′) = r ≡ r′
  Above (suc n) (e ∷ r) (e′ ∷ r′) = Above n r r′

  private
    hd = hdT 𝕄
    tl = tlT 𝕄

  private
    -- Row r⁺ is forced by row r⁻ and the rows above.
    det-tail : ∀ {m} j u v v′ (r : Tb m) → Cnd K L j (u , v) r → Cnd K L j (u , v′) r →
               Last K L ((u , v) ∷ r) → Last K L ((u , v′) ∷ r) → v ≡ v′
    det-tail j u v v′ []            _          _           p q = trans (sym p) q
    det-tail j u v v′ ((a , b) ∷ r) ((_ , _ , ba , _) , _) ((_ , _ , ba′ , _) , _) _ _ =
      cancel v v′ (∂⁻ a) (trans (⊕-comm v (∂⁻ a)) (trans (sym ba) (trans ba′ (⊕-comm (∂⁻ a) v′))))

    hd-pair : ∀ {m} {a b c d : M} {r r′ : Tb m} →
              _≡_ {A = Tb (suc m)} ((a , b) ∷ r) ((c , d) ∷ r′) → a ≡ c
    hd-pair p = cong (λ x → fst (hd x)) p

    detC : ∀ {m} n j (x y : Tb (suc m)) → Cnd K L j (hd x) (tl x) → Cnd K L j (hd y) (tl y) →
           Last K L x → Last K L y → srcT 𝕄 n x ≡ srcT 𝕄 n y → Above n x y → x ≡ y
    detC zero j ((u , v) ∷ r) ((u′ , v′) ∷ r′) cx cy lx ly s refl with hd-pair s
    ... | refl = cong (λ w → (u , w) ∷ r) (det-tail j u v v′ r cx cy lx ly)
    detC (suc n) j (e ∷ []) (e′ ∷ []) cx cy lx ly s a = cong (λ x → hd x ∷ []) s
    detC (suc n) j (e ∷ (f ∷ r)) (e′ ∷ (f′ ∷ r′)) cx cy lx ly s a with cong hd s
    ... | refl = cong (e ∷_) (detC n (suc j) (f ∷ r) (f′ ∷ r′) (snd cx) (snd cy) lx ly (cong tl s) a)

  det : ∀ n x y → IsCell K L x → IsCell K L y → srcT 𝕄 n x ≡ srcT 𝕄 n y → Above n x y → x ≡ y
  det n (e ∷ r) (e′ ∷ r′) (_ , cx , lx) (_ , cy , ly) s a = detC n 1 (e ∷ r) (e′ ∷ r′) cx cy lx ly s a

  ----------------------------------------------------------------------
  -- Fixed-list uniqueness: the factors of a composite are determined
  -- by the composite and their rows above r.

  factors : ∀ r (y z y′ z′ : Tb (suc L)) → IsCell K L y → IsCell K L z → IsCell K L y′ → IsCell K L z′ →
            tgtT 𝕄 r y ≡ srcT 𝕄 r z → tgtT 𝕄 r y′ ≡ srcT 𝕄 r z′ →
            compT 𝕄 r y z ≡ compT 𝕄 r y′ z′ → Above r y y′ → Above r z z′ → (y ≡ y′) × (z ≡ z′)
  factors r y z y′ z′ cy cz cy′ cz′ p p′ e ay az = yy , zz
    where
    yy : y ≡ y′
    yy = det r y y′ cy cy′
           (trans (sym (s-comp 𝕄 r y z)) (trans (cong (srcT 𝕄 r) e) (s-comp 𝕄 r y′ z′))) ay
    zz : z ≡ z′
    zz = det r z z′ cz cz′ (trans (sym p) (trans (cong (tgtT 𝕄 r) yy) p′)) az
