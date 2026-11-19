------------------------------------------------------------------------
-- Cells as towers (Strict.Cell) are cells of ν as a strict ω-category
-- (Strict.Nu) (ledger A5, N3).
--
-- The strict model of L (Strict.L, Strict.Soundness) stores an n-cell
-- of ν(K) as a tower of bags: `step S U c` with source S, target U and
-- top chain c. Strict.Nu stores it as a table of pairs (x_j⁻, x_j⁺) in
-- a cancellative monoid, and makes these tables a strict ω-category
-- `nu K L` (cells of dimension < L), the input of `OmegaSound`.
--
-- For a complex on bags (∂, Bas) with a decidable basis predicate isB
-- (`Bas k w → isB k w`), `TowerNu` reads a tower X as the table
--   entry j = (top of the j-source of X, top of the j-target of X)
-- for j below the dimension, (c, c) at the dimension and zero above,
-- with the bags sorted (Strict.SortBag; `BagADC ∂ isB` is the ADC).
-- `cell→`: every tower cell of dimension n ≤ L is a cell of
-- `nu (BagADC.adc ∂ isB) L`.
------------------------------------------------------------------------
module CaTTExp.Strict.TowerNu where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.SortBag
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; Tri; tri; tri<; tri≡; tri>; ≤-refl; ≤-suc; <-irrefl; ≤-<-⊥)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_; Tab)
import CaTTExp.Strict.Nu as Nu

------------------------------------------------------------------------
-- Entries of a tower.

dimW : Tower → Nat
dimW (base _)     = 0
dimW (step S _ _) = suc (dimW S)

stepE : ∀ {j n} → Bag → Bag → Bag → Tri j n → Bag × Bag
stepE a b c (tri< _) = a , b
stepE a b c (tri≡ _) = c , c
stepE a b c (tri> _) = [] , []

-- entry j = (x_j⁻, x_j⁺).
entW : Tower → Nat → Bag × Bag
entW (base c)     zero    = c , c
entW (base c)     (suc j) = [] , []
entW (step S U c) j       = stepE (fst (entW S j)) (snd (entW U j)) c (tri j (suc (dimW S)))

infix 4 _≈²_
_≈²_ : Bag × Bag → Bag × Bag → Set
p ≈² q = (fst p ≈ fst q) × (snd p ≈ snd q)

private
  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  <→≢ : ∀ {j n} → j < n → j ≡ n → ⊥
  <→≢ p refl = <-irrefl p

  <-asym : ∀ {j n} → j < n → n < j → ⊥
  <-asym {j} {n} p q = ≤-<-⊥ (lt→le p) q
    where
    lt→le : ∀ {a b} → a < b → a ≤ b
    lt→le (s≤s z≤n)     = z≤n
    lt→le (s≤s (s≤s p)) = s≤s (lt→le (s≤s p))

  -- j < suc n and suc j ≥ suc n mean j = n.
  ≤s→ : ∀ {j n} → suc j < suc n → j < n
  ≤s→ (s≤s p) = p

  sa<a : ∀ a → suc a < a → ⊥
  sa<a a = ≤-<-⊥ (≤-suc (≤-refl a))

  a≢sa : ∀ a → a ≡ suc a → ⊥
  a≢sa a e = <-irrefl (subst (a <_) (sym e) (≤-refl (suc a)))

  pl : ∀ {a b} → suc a < b → a < b
  pl (s≤s r) = ≤-suc r

  T→≡ : ∀ b → T b → b ≡ true
  T→≡ true _ = refl

stepE-low : ∀ {j n} a b c (t : Tri j n) → j < n → stepE a b c t ≡ (a , b)
stepE-low a b c (tri< _) _ = refl
stepE-low a b c (tri≡ e) l = ⊥-elim (<→≢ l e)
stepE-low a b c (tri> q) l = ⊥-elim (<-asym l q)

stepE-diag : ∀ {n} a b c (t : Tri n n) → stepE a b c t ≡ (c , c)
stepE-diag a b c (tri< p) = ⊥-elim (<-irrefl p)
stepE-diag a b c (tri≡ _) = refl
stepE-diag a b c (tri> p) = ⊥-elim (<-irrefl p)

stepE-≈ : ∀ {j n n′} {a b c a′ b′ c′} (t : Tri j n) (t′ : Tri j n′) → n ≡ n′ →
          a ≈ a′ → b ≈ b′ → c ≈ c′ → stepE a b c t ≈² stepE a′ b′ c′ t′
stepE-≈ (tri< _) (tri< _) e pa pb pc = pa , pb
stepE-≈ (tri≡ _) (tri≡ _) e pa pb pc = pc , pc
stepE-≈ (tri> _) (tri> _) e pa pb pc = ≈-refl , ≈-refl
stepE-≈ (tri< p) (tri≡ q) refl _ _ _ = ⊥-elim (<→≢ p q)
stepE-≈ (tri< p) (tri> q) refl _ _ _ = ⊥-elim (<-asym p q)
stepE-≈ (tri≡ p) (tri< q) refl _ _ _ = ⊥-elim (<→≢ q p)
stepE-≈ (tri≡ p) (tri> q) refl _ _ _ = ⊥-elim (<→≢ q (sym p))
stepE-≈ (tri> p) (tri< q) refl _ _ _ = ⊥-elim (<-asym q p)
stepE-≈ (tri> p) (tri≡ q) refl _ _ _ = ⊥-elim (<→≢ p (sym q))

≈w-dim : ∀ X Y → X ≈w Y → dimW X ≡ dimW Y
≈w-dim (base _)     (base _)       _       = refl
≈w-dim (step S U _) (step S′ U′ _) (p , _) = cong suc (≈w-dim S S′ p)

ent-≈w : ∀ X Y → X ≈w Y → ∀ j → entW X j ≈² entW Y j
ent-≈w (base c)     (base c′)      p            zero    = p , p
ent-≈w (base c)     (base c′)      p            (suc j) = ≈-refl , ≈-refl
ent-≈w (step S U c) (step S′ U′ c′) (pS , pU , pc) j =
  stepE-≈ (tri j (suc (dimW S))) (tri j (suc (dimW S′))) (cong suc (≈w-dim S S′ pS))
          (fst (ent-≈w S S′ pS j)) (snd (ent-≈w U U′ pU j)) pc

ent-top : ∀ X → entW X (dimW X) ≡ (top X , top X)
ent-top (base c)     = refl
ent-top (step S U c) = stepE-diag _ _ c (tri (suc (dimW S)) (suc (dimW S)))

ent-step-low : ∀ S U c j → j < suc (dimW S) → entW (step S U c) j ≡ (fst (entW S j) , snd (entW U j))
ent-step-low S U c j l = stepE-low _ _ c (tri j (suc (dimW S))) l

-- Source and target share their entries below their dimension.
par-low : ∀ S U → Par S U → ∀ j → j < dimW S → entW S j ≈² entW U j
par-low (base _)       (base _)       _       j ()
par-low (step S₁ S₂ s) (step U₁ U₂ u) (p₁ , p₂) j l =
  subst (λ q → q ≈² entW (step U₁ U₂ u) j) (sym (ent-step-low S₁ S₂ s j l))
    (subst (λ q → (fst (entW S₁ j) , snd (entW S₂ j)) ≈² q)
           (sym (ent-step-low U₁ U₂ u j (subst (λ m → j < suc m) (≈w-dim S₁ U₁ p₁) l)))
           (fst (ent-≈w S₁ U₁ p₁ j) , snd (ent-≈w S₂ U₂ p₂ j)))

-- Above the dimension, the two sides agree.
ent-last : ∀ X j → dimW X ≤ j → fst (entW X j) ≡ snd (entW X j)
ent-last (base c)     zero    _ = refl
ent-last (base c)     (suc j) _ = refl
ent-last (step S U c) j       l with tri j (suc (dimW S))
... | tri< p = ⊥-elim (≤-<-⊥ l p)
... | tri≡ _ = refl
... | tri> _ = refl

------------------------------------------------------------------------
-- The tower conditions, entry by entry.

module TowerNu (∂ : Bool → Tuple → Bag) (isB : Nat → Tuple → Bool) (Bas : Nat → Tuple → Set)
               (B→ : ∀ k w → Bas k w → T (isB k w)) where
  open Cells ∂ Bas
  open BagADC ∂ isB

  K : Nu.ADC
  K = adc

  ChainEq-cong : ∀ {c s u s′ u′} → s ≈ s′ → u ≈ u′ → ChainEq c s u → ChainEq c s′ u′
  ChainEq-cong {c} ps pu h =
    ≈-trans (++-cong (≈-refl {∂B true c}) (≈-sym ps)) (≈-trans h (++-cong (≈-refl {∂B false c}) pu))

  -- Steiner's conditions between consecutive entries, on bags.
  EntB : Nat → Bag × Bag → Bag × Bag → Set
  EntB k p q = All (Bas k) (fst q) × All (Bas k) (snd q) × ChainEq (fst q) (fst p) (snd p) × ChainEq (snd q) (fst p) (snd p)

  IsCell-dim : ∀ n X → IsCell n X → dimW X ≡ n
  IsCell-dim zero    (base c)     _        = refl
  IsCell-dim (suc n) (step S U c) (cS , _) = cong suc (IsCell-dim n S cS)

  private
    ent-top′ : ∀ n S U → IsCell n S → IsCell n U → entW U (dimW S) ≡ (top U , top U)
    ent-top′ n S U cS cU = subst (λ m → entW U m ≡ (top U , top U))
                                 (trans (IsCell-dim n U cU) (sym (IsCell-dim n S cS))) (ent-top U)

    ce0 : ∀ c → ChainEq [] c c
    ce0 c = ≈-refl

    ent-ok-step : ∀ n S U c → IsCell n S → IsCell n U → Par S U → ChainEq c (top S) (top U) → All (Bas (suc n)) c →
                  (∀ j → EntB (suc j) (entW S j) (entW S (suc j))) →
                  (∀ j → EntB (suc j) (entW U j) (entW U (suc j))) →
                  ∀ j → EntB (suc j) (entW (step S U c) j) (entW (step S U c) (suc j))
    ent-ok-step n S U c cS cU par ch bc eS eU j with tri j (suc (dimW S)) | tri (suc j) (suc (dimW S))
    ... | tri< p | tri< q =
      let (b₁ , _ , c₁ , _) = eS j
          (_ , b₂ , _ , c₂) = eU j
          (l₁ , l₂) = par-low S U par j (≤s→ q)
      in b₁ , b₂ , ChainEq-cong {fst (entW S (suc j))} ≈-refl l₂ c₁ ,
                  ChainEq-cong {snd (entW U (suc j))} (≈-sym l₁) ≈-refl c₂
    ... | tri< p | tri≡ q rewrite suc-inj q | ent-top S | ent-top′ n S U cS cU = bc′ , bc′ , ch , ch
      where
      bc′ : All (Bas (suc (dimW S))) c
      bc′ = subst (λ m → All (Bas (suc m)) c) (sym (IsCell-dim n S cS)) bc
    ... | tri< p | tri> q = ⊥-elim (≤-<-⊥ (≤s→′ p) (≤s→ q))
      where
      ≤s→′ : ∀ {a b} → a < suc b → a ≤ b
      ≤s→′ (s≤s r) = r
    ... | tri≡ p | tri< q = ⊥-elim (sa<a _ (subst (_< dimW S) p (≤s→ q)))
    ... | tri≡ p | tri≡ q = ⊥-elim (a≢sa _ (trans (sym (suc-inj q)) p))
    ... | tri≡ p | tri> q = tt , tt , ce0 c , ce0 c
    ... | tri> p | tri< q = ⊥-elim (<-asym (≤s→ q) (pl p))
    ... | tri> p | tri≡ q = ⊥-elim (sa<a _ (subst (suc (dimW S) <_) (suc-inj q) p))
    ... | tri> p | tri> q = tt , tt , ≈-refl , ≈-refl

  ent-ok : ∀ n X → IsCell n X → ∀ j → EntB (suc j) (entW X j) (entW X (suc j))
  ent-ok zero    (base c)     _                         zero    = tt , tt , ce0 c , ce0 c
  ent-ok zero    (base c)     _                         (suc j) = tt , tt , ≈-refl , ≈-refl
  ent-ok (suc n) (step S U c) (cS , cU , par , ch , bc) j       =
    ent-ok-step n S U c cS cU par ch bc (ent-ok n S cS) (ent-ok n U cU) j

  -- The bottom entries are single points.
  Pt : Bag → Set
  Pt c = Σ Tuple λ w → (c ≈ w ∷ []) × Bas zero w

  ent-0 : ∀ n X → IsCell n X → Pt (fst (entW X 0)) × Pt (snd (entW X 0))
  ent-0 zero    (base c)     cw              = cw , cw
  ent-0 (suc n) (step S U c) (cS , cU , _)   rewrite ent-step-low S U c 0 (s≤s z≤n) =
    fst (ent-0 n S cS) , snd (ent-0 n U cU)

  ----------------------------------------------------------------------
  -- Sorted entries satisfy the conditions of Strict.Nu.

  entS : Tower → Nat → SB × SB
  entS X j = mkSB (fst (entW X j)) , mkSB (snd (entW X j))

  private
    filt-all : ∀ k X → All (λ w → T (isB k w)) X → filt (isB k) X ≡ X
    filt-all k []      _        = refl
    filt-all k (x ∷ X) (p , ps) rewrite T→≡ (isB k x) p = cong (x ∷_) (filt-all k X ps)

  InDeg-mk : ∀ L k u → All (Bas k) u → Nu.InDeg K L k (mkSB u)
  InDeg-mk L k u a =
    trans (cong mkSB (filt-all k (sort u) (All-≈ u (sort u) (≈-sym (sort-≈ u)) (All-map u (λ w b → B→ k w b) a))))
          (mkSB-≈ (sort-≈ u))

  Bd-mk : ∀ L u a b → ChainEq u a b → Nu.Bd K L (mkSB a , mkSB b) (mkSB u)
  Bd-mk L u a b h = mkSB-≈
    (≈-trans (++-cong (≈-trans (sort-≈ _) (cm-cong (∂ true) (sort u) u (sort-≈ u))) (sort-≈ a))
    (≈-trans h
             (≈-sym (++-cong (≈-trans (sort-≈ _) (cm-cong (∂ false) (sort u) u (sort-≈ u))) (sort-≈ b)))))

  aug-mk : ∀ c → Pt c → augS (mkSB c) ≡ 1
  aug-mk c (w , p , b) rewrite norm-≈ p | T→≡ (isB zero w) (B→ zero w b) = refl

  Ent-mk : ∀ L k p q → EntB k p q → Nu.Ent K L k (mkSB (fst p) , mkSB (snd p)) (mkSB (fst q) , mkSB (snd q))
  Ent-mk L k p q (b₁ , b₂ , c₁ , c₂) =
    InDeg-mk L k (fst q) b₁ , InDeg-mk L k (snd q) b₂ ,
    Bd-mk L (fst q) (fst p) (snd p) c₁ , Bd-mk L (snd q) (fst p) (snd p) c₂

  Ent0-mk : ∀ L u v → Pt u → Pt v → Nu.Ent0 K L (mkSB u , mkSB v)
  Ent0-mk L u v pu pv =
    InDeg-mk L zero u (All-≈ (fst pu ∷ []) u (≈-sym (fst (snd pu))) (snd (snd pu) , tt)) ,
    InDeg-mk L zero v (All-≈ (fst pv ∷ []) v (≈-sym (fst (snd pv))) (snd (snd pv) , tt)) ,
    aug-mk u pu , aug-mk v pv

  ----------------------------------------------------------------------
  -- Tables.

  tabF : ∀ {m} → (Nat → SB × SB) → Nat → Tab SBMon m
  tabF {zero}  f j = []
  tabF {suc m} f j = f j ∷ tabF f (suc j)

  Cnd-tab : ∀ {m} L (f : Nat → SB × SB) → (∀ j → Nu.Ent K L (suc j) (f j) (f (suc j))) →
            ∀ j → Nu.Cnd K L (suc j) (f j) (tabF {m} f (suc j))
  Cnd-tab {zero}  L f h j = tt
  Cnd-tab {suc m} L f h j = h j , Cnd-tab {m} L f h (suc j)

  Last-tab : ∀ L m (f : Nat → SB × SB) j → fst (f (m + j)) ≡ snd (f (m + j)) → Nu.Last K L (tabF {suc m} f j)
  Last-tab L zero    f j p = p
  Last-tab L (suc m) f j p = Last-tab L m f (suc j) (subst (λ q → fst (f q) ≡ snd (f q)) (sym (+-suc m j)) p)

  tabOf : (L : Nat) → Tower → Tab SBMon (suc L)
  tabOf L X = tabF (entS X) 0

  -- Every tower cell of dimension ≤ L is a cell of ν(K) as a strict ω-category.
  cell→ : ∀ L n X → n ≤ L → IsCell n X → Nu.IsCell K L (tabOf L X)
  cell→ L n X nL cX =
    Ent0-mk L (fst (entW X 0)) (snd (entW X 0)) (fst (ent-0 n X cX)) (snd (ent-0 n X cX)) ,
    Cnd-tab {L} L (entS X) (λ j → Ent-mk L (suc j) (entW X j) (entW X (suc j)) (ent-ok n X cX j)) 0 ,
    Last-tab L L (entS X) 0 (cong mkSB (ent-last X (L + 0) dl))
    where
    dl : dimW X ≤ L + 0
    dl = subst (dimW X ≤_) (sym (+-zero L)) (subst (_≤ L) (sym (IsCell-dim n X cX)) nL)

  cellν : ∀ L n X → n ≤ L → IsCell n X → Nu.Cell K L
  cellν L n X nL cX = tabOf L X , cell→ L n X nL cX
