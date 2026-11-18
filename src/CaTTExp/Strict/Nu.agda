------------------------------------------------------------------------
-- Steiner's ν(K) as a strict ω-category (ledger A5, step N0).
--
-- An augmented directed complex is given abstractly (`ADC`): a
-- cancellative commutative monoid M of non-negative chains (all degrees
-- together), additive maps ∂⁺, ∂⁻ : M → M (the positive and negative
-- parts of the boundary of a basis element, extended additively), an
-- additive projection πⱼ onto degree j, and the augmentation ε. With M
-- the free commutative monoid on a basis this is Steiner's K*.
--
-- A cell of dimension < L is a table x of length L (CaTTExp.Strict.
-- Tables) with
--   * xⱼ^± of degree j;
--   * ε(x₀⁻) = ε(x₀⁺) = 1;
--   * ∂xⱼ^α = xⱼ₋₁⁺ − xⱼ₋₁⁻ for j ≥ 1, written ∂⁺xⱼ^α + xⱼ₋₁⁻ = ∂⁻xⱼ^α + xⱼ₋₁⁺;
--   * the last entry has x⁻ = x⁺.
-- This is Steiner's definition (Omega-categories and chain complexes,
-- 2004, Def. 2.2; Ara–Maltsiniotis 1607.00668 §2.4): a table with
-- entries zero above n has, by the boundary condition at n+1, xₙ⁻ = xₙ⁺.
-- So these are exactly the cells of ν(K) of dimension < L, and for a
-- complex of dimension < L all of them.
--
-- `nu L` is the strict ω-category of these cells, a sub-ω-category of
-- all tables (CaTTExp.Strict.Tables.tables): cells are closed under
-- boundaries and composites. Nothing is postulated.
------------------------------------------------------------------------
module CaTTExp.Strict.Nu where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables

record ADC : Set₁ where
  field
    𝕄      : CMon
  open CMon 𝕄 public
  field
    cancel : ∀ a b c → a ⊕ c ≡ b ⊕ c → a ≡ b
    ∂⁺ ∂⁻  : M → M
    ∂⁺-ε   : ∂⁺ ε ≡ ε
    ∂⁻-ε   : ∂⁻ ε ≡ ε
    ∂⁺-⊕   : ∀ a b → ∂⁺ (a ⊕ b) ≡ ∂⁺ a ⊕ ∂⁺ b
    ∂⁻-⊕   : ∀ a b → ∂⁻ (a ⊕ b) ≡ ∂⁻ a ⊕ ∂⁻ b
    π      : Nat → M → M
    π-ε    : ∀ j → π j ε ≡ ε
    π-⊕    : ∀ j a b → π j (a ⊕ b) ≡ π j a ⊕ π j b
    aug    : M → Nat

module _ (K : ADC) (L : Nat) where
  open ADC K

  private
    P′ = P 𝕄
    Tb = Tab 𝕄
    z  = zeros 𝕄
    ad = add 𝕄

  InDeg : Nat → M → Set
  InDeg j u = π j u ≡ u

  Bd : P′ → M → Set
  Bd (p⁻ , p⁺) u = ∂⁺ u ⊕ p⁻ ≡ ∂⁻ u ⊕ p⁺

  Ent : Nat → P′ → P′ → Set
  Ent j p (u , v) = InDeg j u × InDeg j v × Bd p u × Bd p v

  Cnd : ∀ {m} → Nat → P′ → Tb m → Set
  Cnd j p []      = ⊤
  Cnd j p (e ∷ r) = Ent j p e × Cnd (suc j) e r

  Last : ∀ {m} → Tb (suc m) → Set
  Last ((u , v) ∷ []) = u ≡ v
  Last (e ∷ (e′ ∷ r)) = Last (e′ ∷ r)

  Ent0 : P′ → Set
  Ent0 (u , v) = InDeg 0 u × InDeg 0 v × (aug u ≡ 1) × (aug v ≡ 1)

  IsCell : Tb (suc L) → Set
  IsCell (e ∷ r) = Ent0 e × Cnd 1 e r × Last (e ∷ r)

  ----------------------------------------------------------------------
  -- Monoid bookkeeping.

  private
    mid : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
    mid a b c d =
      trans (⊕-assoc a b (c ⊕ d))
        (trans (cong (a ⊕_) (trans (sym (⊕-assoc b c d)) (trans (cong (_⊕ d) (⊕-comm b c)) (⊕-assoc c b d))))
               (sym (⊕-assoc a c (b ⊕ d))))

  -- Sum of two boundary equations.
  Bd-add : ∀ p p′ u u′ → Bd p u → Bd p′ u′ → Bd (_+P_ 𝕄 p p′) (u ⊕ u′)
  Bd-add (a , b) (c , d) u u′ e e′ =
    trans (cong (_⊕ (a ⊕ c)) (∂⁺-⊕ u u′))
      (trans (mid (∂⁺ u) (∂⁺ u′) a c)
        (trans (cong₂ _⊕_ e e′)
          (trans (mid (∂⁻ u) b (∂⁻ u′) d) (cong (_⊕ (b ⊕ d)) (sym (∂⁻-⊕ u u′))))))

  -- Gluing: u → v and v → w give u → w.
  Bd-glue : ∀ u v w x x′ → Bd (u , v) x → Bd (v , w) x′ → Bd (u , w) (x ⊕ x′)
  Bd-glue u v w x x′ e e′ = cancel _ _ v
    (trans (cong (λ q → (q ⊕ u) ⊕ v) (∂⁺-⊕ x x′))
    (trans (lhs-shuffle)
    (trans (cong₂ _⊕_ e e′)
    (trans rhs-shuffle
    (cong (λ q → (q ⊕ w) ⊕ v) (sym (∂⁻-⊕ x x′)))))))
    where
    -- ((∂⁺x ⊕ ∂⁺x′) ⊕ u) ⊕ v ≡ (∂⁺x ⊕ u) ⊕ (∂⁺x′ ⊕ v)
    lhs-shuffle : ((∂⁺ x ⊕ ∂⁺ x′) ⊕ u) ⊕ v ≡ (∂⁺ x ⊕ u) ⊕ (∂⁺ x′ ⊕ v)
    lhs-shuffle = trans (cong (_⊕ v) (trans (⊕-assoc (∂⁺ x) (∂⁺ x′) u)
                          (trans (cong (∂⁺ x ⊕_) (⊕-comm (∂⁺ x′) u)) (sym (⊕-assoc (∂⁺ x) u (∂⁺ x′))))))
                        (⊕-assoc (∂⁺ x ⊕ u) (∂⁺ x′) v)
    -- (∂⁻x ⊕ v) ⊕ (∂⁻x′ ⊕ w) ≡ ((∂⁻x ⊕ ∂⁻x′) ⊕ w) ⊕ v
    rhs-shuffle : (∂⁻ x ⊕ v) ⊕ (∂⁻ x′ ⊕ w) ≡ ((∂⁻ x ⊕ ∂⁻ x′) ⊕ w) ⊕ v
    rhs-shuffle =
      trans (mid (∂⁻ x) v (∂⁻ x′) w)
        (trans (cong ((∂⁻ x ⊕ ∂⁻ x′) ⊕_) (⊕-comm v w))
          (sym (⊕-assoc (∂⁻ x ⊕ ∂⁻ x′) w v)))

  InDeg-ε : ∀ j → InDeg j ε
  InDeg-ε j = π-ε j

  InDeg-⊕ : ∀ j u v → InDeg j u → InDeg j v → InDeg j (u ⊕ v)
  InDeg-⊕ j u v p q = trans (π-⊕ j u v) (cong₂ _⊕_ p q)

  Bd-ε : ∀ a → Bd (a , a) ε
  Bd-ε a = trans (cong (_⊕ a) ∂⁺-ε) (cong (_⊕ a) (sym ∂⁻-ε))

  ----------------------------------------------------------------------
  -- Closure under boundaries.

  Cnd-zeros : ∀ {m} j a → Cnd {m} j (a , a) z
  Cnd-zeros {zero}  j a = tt
  Cnd-zeros {suc m} j a = (InDeg-ε j , InDeg-ε j , Bd-ε a , Bd-ε a) , Cnd-zeros (suc j) ε

  Last-zeros : ∀ {m} a → Last {m} ((a , a) ∷ z)
  Last-zeros {zero}  a = refl
  Last-zeros {suc m} a = Last-zeros {m} ε

  Cnd-src : ∀ {m} n j p (x : Tb m) → Cnd j p x → Cnd j p (srcT 𝕄 n x)
  Cnd-src n       j p []            c = tt
  Cnd-src zero    j p ((u , v) ∷ r) ((du , dv , bu , bv) , c) = (du , du , bu , bu) , Cnd-zeros (suc j) u
  Cnd-src (suc n) j p (e ∷ r)       (h , c) = h , Cnd-src n (suc j) e r c

  Cnd-tgt : ∀ {m} n j p (x : Tb m) → Cnd j p x → Cnd j p (tgtT 𝕄 n x)
  Cnd-tgt n       j p []            c = tt
  Cnd-tgt zero    j p ((u , v) ∷ r) ((du , dv , bu , bv) , c) = (dv , dv , bv , bv) , Cnd-zeros (suc j) v
  Cnd-tgt (suc n) j p (e ∷ r)       (h , c) = h , Cnd-tgt n (suc j) e r c

  Last-cons : ∀ {m} e (x : Tb (suc m)) → Last x → Last (e ∷ x)
  Last-cons e (f ∷ r) l = l

  Last-src : ∀ {m} n (x : Tb (suc m)) → Last x → Last (srcT 𝕄 n x)
  Last-src {m} zero ((u , v) ∷ r) l = Last-zeros {m} u
  Last-src (suc n) ((u , v) ∷ []) l = l
  Last-src (suc n) (e ∷ (e′ ∷ r)) l = Last-cons e (srcT 𝕄 n (e′ ∷ r)) (Last-src n (e′ ∷ r) l)

  Last-tgt : ∀ {m} n (x : Tb (suc m)) → Last x → Last (tgtT 𝕄 n x)
  Last-tgt {m} zero ((u , v) ∷ r) l = Last-zeros {m} v
  Last-tgt (suc n) ((u , v) ∷ []) l = l
  Last-tgt (suc n) (e ∷ (e′ ∷ r)) l = Last-cons e (tgtT 𝕄 n (e′ ∷ r)) (Last-tgt n (e′ ∷ r) l)

  ----------------------------------------------------------------------
  -- Closure under composites.

  Cnd-add : ∀ {m} j p p′ (r r′ : Tb m) → Cnd j p r → Cnd j p′ r′ → Cnd j (_+P_ 𝕄 p p′) (ad r r′)
  Cnd-add j p p′ [] [] _ _ = tt
  Cnd-add j p p′ ((u , v) ∷ r) ((u′ , v′) ∷ r′) ((du , dv , bu , bv) , c) ((du′ , dv′ , bu′ , bv′) , c′) =
    (InDeg-⊕ j u u′ du du′ , InDeg-⊕ j v v′ dv dv′ , Bd-add p p′ u u′ bu bu′ , Bd-add p p′ v v′ bv bv′) ,
    Cnd-add (suc j) (u , v) (u′ , v′) r r′ c c′

  Cnd-glue : ∀ {m} j u v w (r r′ : Tb m) → Cnd j (u , v) r → Cnd j (v , w) r′ → Cnd j (u , w) (ad r r′)
  Cnd-glue j u v w [] [] _ _ = tt
  Cnd-glue j u v w ((a , b) ∷ r) ((a′ , b′) ∷ r′) ((da , db , ba , bb) , c) ((da′ , db′ , ba′ , bb′) , c′) =
    (InDeg-⊕ j a a′ da da′ , InDeg-⊕ j b b′ db db′ ,
     Bd-glue u v w a a′ ba ba′ , Bd-glue u v w b b′ bb bb′) ,
    Cnd-add (suc j) (a , b) (a′ , b′) r r′ c c′

  private
    hdN : ∀ {m} {e e′ : P′} {r r′ : Tb m} → _≡_ {A = Tb (suc m)} (e ∷ r) (e′ ∷ r′) → e ≡ e′
    hdN refl = refl

    tlN : ∀ {m} {e e′ : P′} {r r′ : Tb m} → _≡_ {A = Tb (suc m)} (e ∷ r) (e′ ∷ r′) → r ≡ r′
    tlN refl = refl

    snd-fst : ∀ {a b c d : M} → (b , b) ≡ (c , c) → b ≡ c
    snd-fst refl = refl

  Cnd-comp : ∀ {m} n j p (x y : Tb m) → tgtT 𝕄 n x ≡ srcT 𝕄 n y → Cnd j p x → Cnd j p y →
             Cnd j p (compT 𝕄 n x y)
  Cnd-comp n       j p []            []              q c c′ = tt
  Cnd-comp zero    j p ((u , v) ∷ r) ((v′ , w) ∷ r′) q ((du , dv , bu , bv) , c) ((dv′ , dw , bv′ , bw) , c′)
    with snd-fst {a = u} {d = w} (hdN q)
  ... | refl = (du , dw , bu , bw) , Cnd-glue (suc j) u v w r r′ c c′
  Cnd-comp (suc n) j p (e ∷ r)       (e′ ∷ r′)       q (h , c) (h′ , c′) with hdN q
  ... | refl = h , Cnd-comp n (suc j) e r r′ (tlN q) c c′

  Last-add : ∀ {m} (r r′ : Tb (suc m)) → Last r → Last r′ → Last (ad r r′)
  Last-add ((u , v) ∷ []) ((u′ , v′) ∷ []) l l′ = cong₂ _⊕_ l l′
  Last-add (e ∷ (f ∷ r)) (e′ ∷ (f′ ∷ r′)) l l′ = Last-add (f ∷ r) (f′ ∷ r′) l l′

  Last-comp : ∀ {m} n (x y : Tb (suc m)) → tgtT 𝕄 n x ≡ srcT 𝕄 n y → Last x → Last y →
              Last (compT 𝕄 n x y)
  Last-comp zero ((u , v) ∷ []) ((v′ , w) ∷ []) q l l′ = trans l (trans (snd-fst {a = u} {d = w} (hdN q)) l′)
  Last-comp zero ((u , v) ∷ (f ∷ r)) ((v′ , w) ∷ (f′ ∷ r′)) q l l′ = Last-add (f ∷ r) (f′ ∷ r′) l l′
  Last-comp (suc n) (e ∷ []) (e′ ∷ []) q l l′ = l
  Last-comp (suc n) (e ∷ (f ∷ r)) (e′ ∷ (f′ ∷ r′)) q l l′ =
    Last-cons e (compT 𝕄 n (f ∷ r) (f′ ∷ r′)) (Last-comp n (f ∷ r) (f′ ∷ r′) (tlN q) l l′)

  cell-src : ∀ n x → IsCell x → IsCell (srcT 𝕄 n x)
  cell-src zero    ((u , v) ∷ r) ((du , dv , au , av) , c , l) =
    (du , du , au , au) , Cnd-zeros 1 u , Last-zeros {L} u
  cell-src (suc n) (e ∷ r) (h , c , l) = h , Cnd-src n 1 e r c , Last-src (suc n) (e ∷ r) l

  cell-tgt : ∀ n x → IsCell x → IsCell (tgtT 𝕄 n x)
  cell-tgt zero    ((u , v) ∷ r) ((du , dv , au , av) , c , l) =
    (dv , dv , av , av) , Cnd-zeros 1 v , Last-zeros {L} v
  cell-tgt (suc n) (e ∷ r) (h , c , l) = h , Cnd-tgt n 1 e r c , Last-tgt (suc n) (e ∷ r) l

  cell-comp : ∀ n x y → tgtT 𝕄 n x ≡ srcT 𝕄 n y → IsCell x → IsCell y → IsCell (compT 𝕄 n x y)
  cell-comp zero ((u , v) ∷ r) ((v′ , w) ∷ r′) q ((du , dv , au , av) , c , l) ((dv′ , dw , av′ , aw) , c′ , l′)
    with snd-fst {a = u} {d = w} (hdN q)
  ... | refl = (du , dw , au , aw) , Cnd-glue 1 u v w r r′ c c′ ,
               Last-comp zero ((u , v) ∷ r) ((v , w) ∷ r′) q l l′
  cell-comp (suc n) (e ∷ r) (e′ ∷ r′) q (h , c , l) (h′ , c′ , l′) with hdN q
  ... | refl = h , Cnd-comp n 1 e r r′ (tlN q) c c′ , Last-comp (suc n) (e ∷ r) (e ∷ r′) q l l′

  ----------------------------------------------------------------------
  -- Being a cell is a proposition (K gives uniqueness of identity
  -- proofs), so cells are determined by their tables.

  private
    ×-prop : ∀ {A B : Set} → (∀ (a a′ : A) → a ≡ a′) → (∀ (b b′ : B) → b ≡ b′) → ∀ (p q : A × B) → p ≡ q
    ×-prop pa pb (a , b) (a′ , b′) = cong₂ _,_ (pa a a′) (pb b b′)

    ⊤-prop : ∀ (a b : ⊤) → a ≡ b
    ⊤-prop tt tt = refl

  Ent-prop : ∀ j p e (a b : Ent j p e) → a ≡ b
  Ent-prop j p (u , v) = ×-prop uip (×-prop uip (×-prop uip uip))

  Cnd-prop : ∀ {m} j p (x : Tb m) (a b : Cnd j p x) → a ≡ b
  Cnd-prop j p []      = ⊤-prop
  Cnd-prop j p (e ∷ r) = ×-prop (Ent-prop j p e) (Cnd-prop (suc j) e r)

  Last-prop : ∀ {m} (x : Tb (suc m)) (a b : Last x) → a ≡ b
  Last-prop ((u , v) ∷ []) = uip
  Last-prop (e ∷ (f ∷ r))  = Last-prop (f ∷ r)

  IsCell-prop : ∀ x (a b : IsCell x) → a ≡ b
  IsCell-prop ((u , v) ∷ r) = ×-prop (×-prop uip (×-prop uip (×-prop uip uip)))
                                     (×-prop (Cnd-prop 1 (u , v) r) (Last-prop ((u , v) ∷ r)))

  ----------------------------------------------------------------------
  -- ν(K), cells of dimension < L.

  Cell : Set
  Cell = Σ (Tb (suc L)) IsCell

  ≡-cell : ∀ {x y : Cell} → fst x ≡ fst y → x ≡ y
  ≡-cell {x , a} {.x , b} refl = cong (x ,_) (IsCell-prop x a b)

  private
    𝒯 = tables 𝕄 (suc L)
    module 𝒯 = ωCat 𝒯

  nu : ωCat
  nu = record
    { C = Cell
    ; src = λ n x → srcT 𝕄 n (fst x) , cell-src n (fst x) (snd x)
    ; tgt = λ n x → tgtT 𝕄 n (fst x) , cell-tgt n (fst x) (snd x)
    ; comp = λ n x y p → compT 𝕄 n (fst x) (fst y) , cell-comp n (fst x) (fst y) (cong fst p) (snd x) (snd y)
    ; src-src-< = λ x l → ≡-cell (𝒯.src-src-< (fst x) l)
    ; src-tgt-< = λ x l → ≡-cell (𝒯.src-tgt-< (fst x) l)
    ; tgt-src-< = λ x l → ≡-cell (𝒯.tgt-src-< (fst x) l)
    ; tgt-tgt-< = λ x l → ≡-cell (𝒯.tgt-tgt-< (fst x) l)
    ; src-src-≥ = λ x l → ≡-cell (𝒯.src-src-≥ (fst x) l)
    ; tgt-src-≥ = λ x l → ≡-cell (𝒯.tgt-src-≥ (fst x) l)
    ; src-tgt-≥ = λ x l → ≡-cell (𝒯.src-tgt-≥ (fst x) l)
    ; tgt-tgt-≥ = λ x l → ≡-cell (𝒯.tgt-tgt-≥ (fst x) l)
    ; src-comp = λ n x y p → ≡-cell (𝒯.src-comp n (fst x) (fst y) (cong fst p))
    ; tgt-comp = λ n x y p → ≡-cell (𝒯.tgt-comp n (fst x) (fst y) (cong fst p))
    ; src-comp-< = λ x y p l → ≡-cell (𝒯.src-comp-< (fst x) (fst y) (cong fst p) l)
    ; tgt-comp-< = λ x y p l → ≡-cell (𝒯.tgt-comp-< (fst x) (fst y) (cong fst p) l)
    ; src-comp-> = λ x y p l q → ≡-cell (𝒯.src-comp-> (fst x) (fst y) (cong fst p) l (cong fst q))
    ; tgt-comp-> = λ x y p l q → ≡-cell (𝒯.tgt-comp-> (fst x) (fst y) (cong fst p) l (cong fst q))
    ; unit-l = λ n x p → ≡-cell (𝒯.unit-l n (fst x) (cong fst p))
    ; unit-r = λ n x p → ≡-cell (𝒯.unit-r n (fst x) (cong fst p))
    ; assoc = λ n x y z p q p′ q′ → ≡-cell (𝒯.assoc n (fst x) (fst y) (fst z) (cong fst p) (cong fst q) (cong fst p′) (cong fst q′))
    ; interchange = λ x y z w l p q r r₁ r₂ r₃ →
        ≡-cell (𝒯.interchange (fst x) (fst y) (fst z) (fst w) l (cong fst p) (cong fst q) (cong fst r)
                              (cong fst r₁) (cong fst r₂) (cong fst r₃))
    }
