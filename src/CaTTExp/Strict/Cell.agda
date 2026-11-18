------------------------------------------------------------------------
-- Cells of the strict ω-category ν(K) of an augmented directed complex
-- K with a basis, and their transport along chain maps.
--
-- K is given abstractly by
--   ∂   : Bool → Tuple → Bag      positive (true) / negative part of the
--                                 boundary of a basis element,
--   Bas : Nat → Tuple → Set       "is a basis element of degree k".
-- Every degree-0 basis element has augmentation 1.
--
-- A cell is stored as a tower: an n-cell is `step S U c` with S, U its
-- (n−1)-source and target and c its top chain; a 0-cell is `base c`.
-- IsCell n X is Steiner's definition of an n-cell of ν(K) (Steiner,
-- "Omega-categories and chain complexes", 2004, Def. 2.8; Ara–
-- Maltsiniotis, arXiv 1607.00668, §2.4):
--   * chains are non-negative (automatic: they are bags) and made of
--     basis elements of the right degree;
--   * ∂c = x⁺ − x⁻, written ∂⁺c + x⁻ = ∂⁻c + x⁺;
--   * source and target share their lower parts (globularity);
--   * ε(x₀^±) = 1, i.e. each 0-chain is a single basis element.
------------------------------------------------------------------------
module CaTTExp.Strict.Cell where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag

data Tower : Set where
  base : Bag → Tower
  step : Tower → Tower → Bag → Tower

top : Tower → Bag
top (base c)     = c
top (step _ _ c) = c

-- All chains of a tower (with repetitions).
flat : Tower → Bag
flat (base c)     = c
flat (step S U c) = flat S ++ (flat U ++ c)

mapTw : (Bag → Bag) → Tower → Tower
mapTw f (base c)     = base (f c)
mapTw f (step S U c) = step (mapTw f S) (mapTw f U) (f c)

infix 4 _≈w_
_≈w_ : Tower → Tower → Set
base c     ≈w base c'       = c ≈ c'
step S U c ≈w step S' U' c' = (S ≈w S') × (U ≈w U') × (c ≈ c')
_          ≈w _             = ⊥

≈w-refl : ∀ X → X ≈w X
≈w-refl (base c)     = ≈-refl
≈w-refl (step S U c) = ≈w-refl S , ≈w-refl U , ≈-refl

≈w-sym : ∀ X Y → X ≈w Y → Y ≈w X
≈w-sym (base c)     (base c')       p           = ≈-sym p
≈w-sym (step S U c) (step S' U' c') (p , q , r) = ≈w-sym S S' p , ≈w-sym U U' q , ≈-sym r

≈w-trans : ∀ X Y Z → X ≈w Y → Y ≈w Z → X ≈w Z
≈w-trans (base _)     (base _)     (base _)     p q = ≈-trans p q
≈w-trans (step S U c) (step S' U' c') (step S'' U'' c'') (p , q , r) (p' , q' , r') =
  ≈w-trans S S' S'' p p' , ≈w-trans U U' U'' q q' , ≈-trans r r'

≈w-top : ∀ X Y → X ≈w Y → top X ≈ top Y
≈w-top (base _)     (base _)     p           = p
≈w-top (step _ _ _) (step _ _ _) (_ , _ , r) = r

-- Globularity: source and target have the same lower parts.
Par : Tower → Tower → Set
Par (base _)       (base _)       = ⊤
Par (step S U _)   (step S' U' _) = (S ≈w S') × (U ≈w U')
Par _              _              = ⊥

Par-≈ : ∀ S U S' U' → S ≈w S' → U ≈w U' → Par S U → Par S' U'
Par-≈ (base _) (base _) (base _) (base _) _ _ _ = tt
Par-≈ (step S₁ S₂ _) (step U₁ U₂ _) (step S₁' S₂' _) (step U₁' U₂' _) (p₁ , p₂ , _) (q₁ , q₂ , _) (a , b) =
  ≈w-trans S₁' S₁ U₁' (≈w-sym S₁ S₁' p₁) (≈w-trans S₁ U₁ U₁' a q₁) ,
  ≈w-trans S₂' S₂ U₂' (≈w-sym S₂ S₂' p₂) (≈w-trans S₂ U₂ U₂' b q₂)

mapTw-≈ : ∀ f → (∀ {X Y} → X ≈ Y → f X ≈ f Y) → ∀ X Y → X ≈w Y → mapTw f X ≈w mapTw f Y
mapTw-≈ f fc (base _)     (base _)     p           = fc p
mapTw-≈ f fc (step S U _) (step S' U' _) (p , q , r) = mapTw-≈ f fc S S' p , mapTw-≈ f fc U U' q , fc r

Par-map : ∀ f → (∀ {X Y} → X ≈ Y → f X ≈ f Y) → ∀ S U → Par S U → Par (mapTw f S) (mapTw f U)
Par-map f fc (base _)       (base _)       _       = tt
Par-map f fc (step S₁ S₂ _) (step U₁ U₂ _) (a , b) = mapTw-≈ f fc S₁ U₁ a , mapTw-≈ f fc S₂ U₂ b

------------------------------------------------------------------------
-- Cells of ν(K).

module Cells (∂ : Bool → Tuple → Bag) (Bas : Nat → Tuple → Set) where

  ∂B : Bool → Bag → Bag
  ∂B b = cm (∂ b)

  ChainEq : Bag → Bag → Bag → Set
  ChainEq c s u = ∂B true c ++ s ≈ ∂B false c ++ u

  IsCell : Nat → Tower → Set
  IsCell zero    (base c)     = Σ Tuple λ w → (c ≈ w ∷ []) × Bas zero w
  IsCell (suc n) (step S U c) =
    IsCell n S × IsCell n U × Par S U × ChainEq c (top S) (top U) × All (Bas (suc n)) c
  IsCell _       _            = ⊥

  -- The top chain consists of basis elements of the cell's degree.
  IsCell-top : ∀ n X → IsCell n X → All (Bas n) (top X)
  IsCell-top zero    (base c)     (w , p , b) =
    All-≈ (w ∷ []) c (≈-sym p) (b , tt)
  IsCell-top (suc n) (step S U c) (_ , _ , _ , _ , a) = a

  ChainEq-≈ : ∀ {c c' s s' u u'} → c ≈ c' → s ≈ s' → u ≈ u' → ChainEq c s u → ChainEq c' s' u'
  ChainEq-≈ {c} {c'} {s} {s'} {u} {u'} pc ps pu e =
    begin
      ∂B true c' ++ s'
    ≈⟨ ++-cong (cm-cong (∂ true) c' c (≈-sym pc)) (≈-sym ps) ⟩
      ∂B true c ++ s
    ≈⟨ e ⟩
      ∂B false c ++ u
    ≈⟨ ++-cong (cm-cong (∂ false) c c' pc) pu ⟩
      ∂B false c' ++ u'
    ∎

  IsCell-≈ : ∀ n X Y → X ≈w Y → IsCell n X → IsCell n Y
  IsCell-≈ zero (base c) (base c') p (w , q , b) = w , ≈-trans (≈-sym p) q , b
  IsCell-≈ (suc n) (step S U c) (step S' U' c') (pS , pU , pc) (cS , cU , par , ch , a) =
    IsCell-≈ n S S' pS cS , IsCell-≈ n U U' pU cU ,
    Par-≈ S U S' U' pS pU par ,
    ChainEq-≈ pc (≈w-top S S' pS) (≈w-top U U' pU) ch ,
    All-≈ c c' pc a

------------------------------------------------------------------------
-- Transport along a map of complexes given on basis elements.
--
-- F sends a basis element of K to a non-negative chain of K'. If F
-- preserves degrees, augmentation and boundaries, then ν(F), applied
-- chainwise, sends cells of ν(K) to cells of ν(K'). (This is the
-- functoriality of ν on morphisms of augmented directed complexes.)

module Transport
  (∂ : Bool → Tuple → Bag) (Bas : Nat → Tuple → Set)
  (∂' : Bool → Tuple → Bag) (Bas' : Nat → Tuple → Set)
  (F : Tuple → Bag)
  (F-basis : ∀ k w → Bas k w → All (Bas' k) (F w))
  (F-aug   : ∀ w → Bas zero w → Σ Tuple λ w' → F w ≈ w' ∷ [])
  (F-chain : ∀ k w b → Bas k w →
             cm (∂' b) (F w) ++ cm F (∂ (not b) w) ≈ cm (∂' (not b)) (F w) ++ cm F (∂ b w))
  where

  open Cells ∂ Bas renaming (IsCell to IsCellK; ChainEq to ChainEqK)
  open Cells ∂' Bas' renaming (IsCell to IsCellK'; ChainEq to ChainEqK'; ∂B to ∂B')

  f : Bag → Bag
  f = cm F

  f-cong : ∀ {X Y} → X ≈ Y → f X ≈ f Y
  f-cong {X} {Y} = cm-cong F X Y

  -- The chain map property on a bag of basis elements of one degree.
  f-chain : ∀ k b c → All (Bas k) c →
            ∂B' b (f c) ++ f (cm (∂ (not b)) c) ≈ ∂B' (not b) (f c) ++ f (cm (∂ b) c)
  f-chain k b c a =
    begin
      cm (∂' b) (cm F c) ++ cm F (cm (∂ (not b)) c)
    ≈⟨ ≡→≈ (cong₂ _++_ (cm-fuse (∂' b) F c) (cm-fuse F (∂ (not b)) c)) ⟩
      cm (λ w → cm (∂' b) (F w)) c ++ cm (λ w → cm F (∂ (not b) w)) c
    ≈⟨ ≈-sym (cm-sum _ _ c) ⟩
      cm (λ w → cm (∂' b) (F w) ++ cm F (∂ (not b) w)) c
    ≈⟨ cm-ext _ _ c a (λ w bw → F-chain k w b bw) ⟩
      cm (λ w → cm (∂' (not b)) (F w) ++ cm F (∂ b w)) c
    ≈⟨ cm-sum _ _ c ⟩
      cm (λ w → cm (∂' (not b)) (F w)) c ++ cm (λ w → cm F (∂ b w)) c
    ≈⟨ ≡→≈ (sym (cong₂ _++_ (cm-fuse (∂' (not b)) F c) (cm-fuse F (∂ b) c))) ⟩
      cm (∂' (not b)) (cm F c) ++ cm F (cm (∂ b) c)
    ∎

  chain-transport : ∀ k c s u → All (Bas k) c → ChainEqK c s u → ChainEqK' (f c) (f s) (f u)
  chain-transport k c s u a e =
    ++-cancelʳ (P ++ f s) (N ++ f u) (f (cm (∂ false) c))
      (begin
         (P ++ f s) ++ f D⁻
       ≈⟨ ++-assoc P (f s) (f D⁻) ⟩
         P ++ (f s ++ f D⁻)
       ≈⟨ ++-cong (≈-refl {P}) (++-comm (f s) (f D⁻)) ⟩
         P ++ (f D⁻ ++ f s)
       ≈⟨ ≈-sym (++-assoc P (f D⁻) (f s)) ⟩
         (P ++ f D⁻) ++ f s
       ≈⟨ ++-cong (f-chain k true c a) (≈-refl {f s}) ⟩
         (N ++ f D⁺) ++ f s
       ≈⟨ ++-assoc N (f D⁺) (f s) ⟩
         N ++ (f D⁺ ++ f s)
       ≈⟨ ++-cong (≈-refl {N}) (≡→≈ (sym (cm-++ F D⁺ s))) ⟩
         N ++ f (D⁺ ++ s)
       ≈⟨ ++-cong (≈-refl {N}) (f-cong e) ⟩
         N ++ f (D⁻ ++ u)
       ≈⟨ ++-cong (≈-refl {N}) (≡→≈ (cm-++ F D⁻ u)) ⟩
         N ++ (f D⁻ ++ f u)
       ≈⟨ ++-cong (≈-refl {N}) (++-comm (f D⁻) (f u)) ⟩
         N ++ (f u ++ f D⁻)
       ≈⟨ ≈-sym (++-assoc N (f u) (f D⁻)) ⟩
         (N ++ f u) ++ f D⁻
       ∎)
    where
    P = ∂B' true (f c)
    N = ∂B' false (f c)
    D⁻ = cm (∂ false) c
    D⁺ = cm (∂ true) c

  transport : ∀ n X → IsCellK n X → IsCellK' n (mapTw f X)
  transport zero (base c) (w , p , b) =
    let (w' , q) = F-aug w b in
    w' , ≈-trans (f-cong p) (≈-trans (≡→≈ (++-[]L (F w))) q) ,
    All-elem' w' (F w) q (F-basis zero w b)
    where
    All-elem' : ∀ w' X → X ≈ w' ∷ [] → All (Bas' zero) X → Bas' zero w'
    All-elem' w' X q a = fst (All-≈ X (w' ∷ []) q a)
  transport (suc n) (step S U c) (cS , cU , par , ch , a) =
    transport n S cS , transport n U cU ,
    Par-map f f-cong S U par ,
    subst₂ (ChainEqK' (f c)) (top-map S) (top-map U)
      (chain-transport (suc n) c (top S) (top U) a ch) ,
    All-cm F c a (λ w bw → F-basis (suc n) w bw)
    where
    top-map : ∀ X → f (top X) ≡ top (mapTw f X)
    top-map (base _)     = refl
    top-map (step _ _ _) = refl
    subst₂ : ∀ {A : Set} (P : A → A → Set) {x y u v} → x ≡ y → u ≡ v → P x u → P y v
    subst₂ P refl refl p = p
