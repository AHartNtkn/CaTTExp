------------------------------------------------------------------------
-- Well-typed trees over a pasting context, and their supports (ledger
-- item A3a, general case).
--
-- Fix a context Θ whose arrow types are ordered (x < y whenever some
-- variable has type x → y; true of every pasting context). A tree of
-- variables is *well typed at P* (`TV P`) when its spine labels have
-- type P and each branch between spine labels x and y is well typed at
-- x →_P y. Well-typed trees are closed under the operations of the free
-- strict ω-category 𝒯 (truncations, gluing, composites of trees of
-- trees), and they are determined by their sets of labels (`inj`): the
-- spine is the ordered list of labels of type P, and a label belongs to
-- the branch whose left spine label is its iterated source. This is the
-- support injectivity of the outside answer (notes/conjectures/answered/
-- strict-omega-pasting-formal-2026-11-18.md, Lemma 4), for the cells
-- that the proof meets.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega using (_≤_; _<_; z≤n; s≤s; ≤-refl; ≤-suc; ≤-trans; <-irrefl; ≤-<-⊥)

module CaTTExp.Strict.FreeTV (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.LabelSets
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)
open import CaTTExp.Strict.GenericEnv 𝕊 using (vn; discT; disc; 𝒯)
import CaTTExp.Strict.OmegaPasting 𝒯 as P𝒯

------------------------------------------------------------------------
-- Prefixes of types and iterated sources.

data Ext (R : Ty) : Ty → Set where
  ext-refl : Ext R R
  ext-arr  : ∀ {Q s u} → Ext R Q → Ext R (arr Q s u)

ext-up : ∀ {R s u Q} → Ext (arr R s u) Q → Ext R Q
ext-up ext-refl    = ext-arr ext-refl
ext-up (ext-arr e) = ext-arr (ext-up e)

ext-dim : ∀ {R Q} → Ext R Q → dim R ≤ dim Q
ext-dim ext-refl    = ≤-refl _
ext-dim (ext-arr e) = ≤-suc (ext-dim e)

srcTy : Nat → Ty → Nat
srcTy j ⋆           = 0
srcTy j (arr B s u) = if dim B ==ℕ j then vn s else srcTy j B

private
  ==-r : ∀ n → (n ==ℕ n) ≡ true
  ==-r zero    = refl
  ==-r (suc n) = ==-r n

  >-≢ : ∀ a b → suc b ≤ a → (a ==ℕ b) ≡ false
  >-≢ (suc a) zero    _       = refl
  >-≢ (suc a) (suc b) (s≤s p) = >-≢ a b p

  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  <ℕ→< : ∀ a b → T (a <ℕ b) → a < b
  <ℕ→< zero    (suc b) _ = s≤s z≤n
  <ℕ→< (suc a) (suc b) p = s≤s (<ℕ→< a b p)

  <→≤ : ∀ {a b} → a < b → a ≤ b
  <→≤ p = ≤-trans (≤-suc (≤-refl _)) p

  <-trans : ∀ {a b c} → a < b → b < c → a < c
  <-trans p q = ≤-trans p (<→≤ q)

  <-≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
  <-≤-trans p q = ≤-trans p q

  ≤-<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
  ≤-<-trans p (s≤s q) = s≤s (≤-trans p q)

ext-src : ∀ {R s u Q} → Ext (arr R s u) Q → srcTy (dim R) Q ≡ vn s
ext-src {R} ext-refl rewrite ==-r (dim R) = refl
ext-src {R} (ext-arr {Q} e) rewrite >-≢ (dim Q) (dim R) (ext-dim e) = ext-src e

------------------------------------------------------------------------
-- Well-typed trees.

module _ (Θ : Ctx) (ord : ArrOrd Θ) where

  mutual
    TV : Ty → LT Nat → Set
    TV P (node x r) = (lookup Θ x ≡ just P) × TVB P x r

    TVB : Ty → Nat → Br Nat → Set
    TVB P x nil          = ⊤
    TVB P x (cons T y r) = TV (arr P (var x) (var y)) T × (lookup Θ y ≡ just P) × TVB P y r

  -- Consecutive spine labels increase.
  step< : ∀ P x T y → TV (arr P (var x) (var y)) T → x < y
  step< P x (node t _) y (lt , _) = <ℕ→< x y (snd (snd (ord t P x y lt)))

  no-P : ∀ {v P Q s u} → lookup Θ v ≡ just P → lookup Θ v ≡ just Q → Ext (arr P s u) Q → ⊥
  no-P {P = P} p q e with trans (sym p) q
  ... | refl = <-irrefl (ext-dim e)

  ----------------------------------------------------------------------
  -- Types of labels.

  mutual
    lab-ext : ∀ R X v → TV R X → v ∈ flat X → Σ Ty λ Q → (lookup Θ v ≡ just Q) × Ext R Q
    lab-ext R (node x r) v (lx , tb) m with ∈-∷⁻ v x (flatB r) m
    ... | inj₁ refl = R , lx , ext-refl
    ... | inj₂ m′   = labB-ext R x r v tb m′

    labB-ext : ∀ R x r v → TVB R x r → v ∈ flatB r → Σ Ty λ Q → (lookup Θ v ≡ just Q) × Ext R Q
    labB-ext R x nil v _ ()
    labB-ext R x (cons T y r) v (tT , ly , tr) m with ∈-∷⁻ v y (flat T ++ flatB r) m
    ... | inj₁ refl = R , ly , ext-refl
    ... | inj₂ m′ with ∈-++⁻ v (flat T) (flatB r) m′
    ...   | inj₁ mT = let (Q , lq , e) = lab-ext _ T v tT mT in Q , lq , ext-up e
    ...   | inj₂ mr = labB-ext R y r v tr mr

  -- A label after the spine label y is either a later spine label or
  -- sits in a branch whose left spine label is y or later.
  Later : Ty → Nat → Nat → Set
  Later P y v = ((lookup Θ v ≡ just P) × (y < v)) ⊎
                (Σ Ty λ Q → Σ Nat λ s → Σ Nat λ t → (lookup Θ v ≡ just Q) × Ext (arr P (var s) (var t)) Q × (y ≤ s))

  labB : ∀ P y r v → TVB P y r → v ∈ flatB r → Later P y v
  labB P y nil v _ ()
  labB P y (cons T z r) v (tT , lz , tr) m with ∈-∷⁻ v z (flat T ++ flatB r) m
  ... | inj₁ refl = inj₁ (lz , step< P y T z tT)
  ... | inj₂ m′ with ∈-++⁻ v (flat T) (flatB r) m′
  ...   | inj₁ mT = let (Q , lq , e) = lab-ext _ T v tT mT in inj₂ (Q , y , z , lq , e , ≤-refl y)
  ...   | inj₂ mr with labB P z r v tr mr
  ...     | inj₁ (lv , lt)             = inj₁ (lv , <-trans (step< P y T z tT) lt)
  ...     | inj₂ (Q , s , t , lq , e , le) = inj₂ (Q , s , t , lq , e , <→≤ (<-≤-trans (step< P y T z tT) le))

  spine-pos : ∀ P y r v → TVB P y r → lookup Θ v ≡ just P → v ∈ flatB r → y < v
  spine-pos P y r v tr lv m with labB P y r v tr m
  ... | inj₁ (_ , lt)                  = lt
  ... | inj₂ (Q , s , t , lq , e , le) = ⊥-elim (no-P lv lq e)

  -- A label of the branch between x and y is not y and not a label after y.
  sep : ∀ P x y T r v → TV (arr P (var x) (var y)) T → TVB P y r → v ∈ flat T → v ∈ flatB r → ⊥
  sep P x y T r v tT tr mT mr with lab-ext _ T v tT mT | labB P y r v tr mr
  ... | (Q , lq , e) | inj₁ (lv , _) = no-P lv lq e
  ... | (Q , lq , e) | inj₂ (Q′ , s , t , lq′ , e′ , le) with trans (sym lq) lq′
  ...   | refl = ≤-<-⊥ (subst (y ≤_) (trans (sym (ext-src e′)) (ext-src e)) le) (step< P x T y tT)

  sep-y : ∀ P x y T v → TV (arr P (var x) (var y)) T → lookup Θ y ≡ just P → v ∈ flat T → v ≡ y → ⊥
  sep-y P x y T v tT ly mT refl = let (Q , lq , e) = lab-ext _ T v tT mT in no-P ly lq e

  ----------------------------------------------------------------------
  -- Injectivity.

  private
    both : ∀ {a b} → (a ≡ b) ⊎ (b < a) → (b ≡ a) ⊎ (a < b) → a ≡ b
    both (inj₁ e) _        = e
    both (inj₂ _) (inj₁ e) = sym e
    both (inj₂ p) (inj₂ q) = ⊥-elim (<-irrefl (<-trans p q))

    -- A label of type P among b and the labels after it is b or later.
    st : ∀ P a b s → lookup Θ a ≡ just P → TVB P b s → a ∈ (b ∷ flatB s) → (a ≡ b) ⊎ (b < a)
    st P a b s la tb m with ∈-∷⁻ a b (flatB s) m
    ... | inj₁ e  = inj₁ e
    ... | inj₂ m′ = inj₂ (spine-pos P b s a tb la m′)

    first : ∀ P x y y′ T′ r′ → TV (arr P (var x) (var y′)) T′ → TVB P y′ r′ → lookup Θ y ≡ just P →
            y ∈ flatB (cons T′ y′ r′) → (y ≡ y′) ⊎ (y′ < y)
    first P x y y′ T′ r′ tT′ tr′ ly m with ∈-∷⁻ y y′ (flat T′ ++ flatB r′) m
    ... | inj₁ e  = inj₁ e
    ... | inj₂ m′ with ∈-++⁻ y (flat T′) (flatB r′) m′
    ...   | inj₁ mT = let (Q , lq , e) = lab-ext _ T′ y tT′ mT in ⊥-elim (no-P ly lq e)
    ...   | inj₂ mr = inj₂ (spine-pos P y′ r′ y tr′ ly mr)

    tail-incl : ∀ P x r r′ → lookup Θ x ≡ just P → TVB P x r → (x ∷ flatB r) ⊆ (x ∷ flatB r′) → flatB r ⊆ flatB r′
    tail-incl P x r r′ lx tb k = sub h
      where
      h : ∀ v → v ∈ flatB r → v ∈ flatB r′
      h v m with ∈-∷⁻ v x (flatB r′) (app k v (∈-tl v x (flatB r) m))
      ... | inj₁ refl = ⊥-elim (<-irrefl (spine-pos P x r x tb lx m))
      ... | inj₂ m′   = m′

    branch-incl : ∀ P x y T T′ r r′ → TV (arr P (var x) (var y)) T → lookup Θ y ≡ just P → TVB P y r′ →
                  flatB (cons T y r) ⊆ flatB (cons T′ y r′) → flat T ⊆ flat T′
    branch-incl P x y T T′ r r′ tT ly tr′ k = sub h
      where
      h : ∀ v → v ∈ flat T → v ∈ flat T′
      h v mT with ∈-∷⁻ v y (flat T′ ++ flatB r′) (app k v (∈-tl v y (flat T ++ flatB r) (∈-++ˡ v (flat T) (flatB r) mT)))
      ... | inj₁ e  = ⊥-elim (sep-y P x y T v tT ly mT e)
      ... | inj₂ m′ with ∈-++⁻ v (flat T′) (flatB r′) m′
      ...   | inj₁ mT′ = mT′
      ...   | inj₂ mr′ = ⊥-elim (sep P x y T r′ v tT tr′ mT mr′)

    rest-incl : ∀ P x y T r r′ → TV (arr P (var x) (var y)) T → lookup Θ y ≡ just P → TVB P y r →
                flatB (cons T y r) ⊆ flatB (cons T y r′) → flatB r ⊆ flatB r′
    rest-incl P x y T r r′ tT ly tr k = sub h
      where
      h : ∀ v → v ∈ flatB r → v ∈ flatB r′
      h v mr with ∈-∷⁻ v y (flat T ++ flatB r′) (app k v (∈-tl v y (flat T ++ flatB r) (∈-++ʳ v (flat T) (flatB r) mr)))
      ... | inj₁ refl = ⊥-elim (<-irrefl (spine-pos P y r y tr ly mr))
      ... | inj₂ m′ with ∈-++⁻ v (flat T) (flatB r′) m′
      ...   | inj₁ mT  = ⊥-elim (sep P x y T r v tT tr mT mr)
      ...   | inj₂ mr′ = mr′

  mutual
    inj : ∀ P X X′ → TV P X → TV P X′ → flat X ⊆ flat X′ → flat X′ ⊆ flat X → X ≡ X′
    inj P (node x r) (node x′ r′) (lx , tb) (lx′ , tb′) f g =
      root (both (st P x x′ r′ lx tb′ (app f x (∈-hd x (flatB r))))
                 (st P x′ x r lx′ tb (app g x′ (∈-hd x′ (flatB r′)))))
      where
      root : x ≡ x′ → node x r ≡ node x′ r′
      root refl = cong (node x) (injB P x r r′ tb tb′ (tail-incl P x r r′ lx tb f) (tail-incl P x r′ r lx′ tb′ g))

    injB : ∀ P x r r′ → TVB P x r → TVB P x r′ → flatB r ⊆ flatB r′ → flatB r′ ⊆ flatB r → r ≡ r′
    injB P x nil          nil             _ _ f g = refl
    injB P x nil          (cons T′ y′ r′) _ _ f g = ⊥-elim (∉[] {y′} (app g y′ (∈-hd y′ (flat T′ ++ flatB r′))))
    injB P x (cons T y r) nil             _ _ f g = ⊥-elim (∉[] {y} (app f y (∈-hd y (flat T ++ flatB r))))
    injB P x (cons T y r) (cons T′ y′ r′) (tT , ly , tr) (tT′ , ly′ , tr′) f g =
      spine (both (first P x y y′ T′ r′ tT′ tr′ ly (app f y (∈-hd y (flat T ++ flatB r))))
                  (first P x y′ y T r tT tr ly′ (app g y′ (∈-hd y′ (flat T′ ++ flatB r′)))))
      where
      spine : y ≡ y′ → cons T y r ≡ cons T′ y′ r′
      spine refl = br (inj (arr P (var x) (var y)) T T′ tT tT′
                         (branch-incl P x y T T′ r r′ tT ly tr′ f) (branch-incl P x y T′ T r′ r tT′ ly tr g))
        where
        br : T ≡ T′ → cons T y r ≡ cons T′ y r′
        br refl = cong (cons T y) (injB P y r r′ tr tr′
                    (rest-incl P x y T r r′ tT ly tr f) (rest-incl P x y T r′ r tT ly tr′ g))

  ----------------------------------------------------------------------
  -- Equal boundaries in one height force a lower height.

  lastv-ge : ∀ P x r → TVB P x r → x ≤ lastv x r
  lastv-ge P x nil          _              = ≤-refl x
  lastv-ge P x (cons T y r) (tT , _ , tr) = <→≤ (<-≤-trans (step< P x T y tT) (lastv-ge P y r tr))

  mutual
    stab : ∀ i P X → TV P X → bdm i X ≡ bdp i X → bdm (suc i) X ≡ bdm i X
    stab zero    P (node x nil)          _                   e = refl
    stab zero    P (node x (cons T y r)) (_ , tT , _ , tr) e =
      ⊥-elim (<-irrefl (subst (x <_) (sym (node-x e)) (<-≤-trans (step< P x T y tT) (lastv-ge P y r tr))))
    stab (suc i) P (node x r) (_ , tb) e = cong (node x) (stabB i P x r tb (node-r e))

    stabB : ∀ i P x r → TVB P x r → bdmB i r ≡ bdpB i r → bdmB (suc i) r ≡ bdmB i r
    stabB i P x nil          _               e = refl
    stabB i P x (cons T y r) (tT , _ , tr) e =
      cong₂ (λ a b → cons a y b) (stab i _ T tT (cons-T e)) (stabB i P y r tr (cons-r e))

  ----------------------------------------------------------------------
  -- Closure under the operations of 𝒯.

  lastv-ty : ∀ P x r → lookup Θ x ≡ just P → TVB P x r → lookup Θ (lastv x r) ≡ just P
  lastv-ty P x nil          lx _             = lx
  lastv-ty P x (cons T y r) lx (_ , ly , tr) = lastv-ty P y r ly tr

  mutual
    tv-bdm : ∀ n P X → TV P X → TV P (bdm n X)
    tv-bdm zero    P (node x r) (lx , _)  = lx , tt
    tv-bdm (suc n) P (node x r) (lx , tb) = lx , tvB-bdm n P x r tb

    tvB-bdm : ∀ n P x r → TVB P x r → TVB P x (bdmB n r)
    tvB-bdm n P x nil          _               = tt
    tvB-bdm n P x (cons T y r) (tT , ly , tr) = tv-bdm n _ T tT , ly , tvB-bdm n P y r tr

  mutual
    tv-bdp : ∀ n P X → TV P X → TV P (bdp n X)
    tv-bdp zero    P (node x r) (lx , tb) = lastv-ty P x r lx tb , tt
    tv-bdp (suc n) P (node x r) (lx , tb) = lx , tvB-bdp n P x r tb

    tvB-bdp : ∀ n P x r → TVB P x r → TVB P x (bdpB n r)
    tvB-bdp n P x nil          _               = tt
    tvB-bdp n P x (cons T y r) (tT , ly , tr) = tv-bdp n _ T tT , ly , tvB-bdp n P y r tr

  tvB-++ : ∀ P x r₁ r₂ → TVB P x r₁ → TVB P (lastv x r₁) r₂ → TVB P x (r₁ ++B r₂)
  tvB-++ P x nil          r₂ _               t₂ = t₂
  tvB-++ P x (cons T y r) r₂ (tT , ly , tr) t₂ = tT , ly , tvB-++ P y r r₂ tr t₂

  mutual
    tv-glue : ∀ n P X Y → TV P X → TV P Y → bdp n X ≡ bdm n Y → TV P (glue n X Y)
    tv-glue zero P (node x r₁) (node y r₂) (lx , t₁) (ly , t₂) e =
      lx , tvB-++ P x r₁ r₂ t₁ (subst (λ z → TVB P z r₂) (sym (node-x e)) t₂)
    tv-glue (suc n) P (node x r₁) (node y r₂) (lx , t₁) (ly , t₂) e =
      lx , tvB-glue n P x r₁ r₂ t₁ (subst (λ z → TVB P z r₂) (sym (node-x e)) t₂) (node-r e)

    tvB-glue : ∀ n P x r₁ r₂ → TVB P x r₁ → TVB P x r₂ → bdpB n r₁ ≡ bdmB n r₂ → TVB P x (glueB n r₁ r₂)
    tvB-glue n P x nil            _               t₁ t₂ e = tt
    tvB-glue n P x (cons T y r)   nil             t₁ t₂ e = t₁
    tvB-glue n P x (cons T₁ y r₁) (cons T₂ y₂ r₂) (tT₁ , ly , t₁) (tT₂ , ly₂ , t₂) e =
      tv-glue n _ T₁ T₂ tT₁ (subst (λ z → TV (arr P (var x) (var z)) T₂) (sym (cons-y e)) tT₂) (cons-T e) ,
      ly ,
      tvB-glue n P y r₁ r₂ t₁ (subst (λ z → TVB P z r₂) (sym (cons-y e)) t₂) (cons-r e)

  ----------------------------------------------------------------------
  -- Composites of trees of well-typed trees.

  mutual
    AllL : (LT Nat → Set) → LT (LT Nat) → Set
    AllL Pr (node x r) = Pr x × AllLB Pr r

    AllLB : (LT Nat → Set) → Br (LT Nat) → Set
    AllLB Pr nil          = ⊤
    AllLB Pr (cons T y r) = AllL Pr T × Pr y × AllLB Pr r

  module _ {L : Set} (Pr : LT Nat → Set) (g : L → LT Nat) (h : ∀ w → Pr (g w)) where
    mutual
      allL-map : ∀ T → AllL Pr (mapLT g T)
      allL-map (node x r) = h x , allLB-map r

      allLB-map : ∀ r → AllLB Pr (mapB g r)
      allLB-map nil          = tt
      allLB-map (cons T y r) = allL-map T , h y , allLB-map r

  mutual
    cp-tv : ∀ {k U X} → P𝒯.Cp k U X → AllL (TV ⋆) U → TV ⋆ X
    cp-tv (P𝒯.cp u) (tx , tr) = cpB-tv u tx tr

    cpB-tv : ∀ {k x r X} → P𝒯.CpB k x r X → TV ⋆ x → AllLB (TV ⋆) r → TV ⋆ X
    cpB-tv (P𝒯.cnil _) tx _ = tx
    cpB-tv {k} (P𝒯.ccons {a = a} {b = b} ca e cb p) tx (tT , ty , tr) =
      tv-glue k ⋆ a b (cp-tv ca tT) (cpB-tv cb ty tr) p

------------------------------------------------------------------------
-- Labels under the operations of 𝒯.

lastv-∈ : ∀ x r → lastv x r ∈ flat (node x r)
lastv-∈ x nil          = ∈-hd x []
lastv-∈ x (cons T y r) =
  ∈⊆ (lastv-∈ y r) (tl⊆ x (⊆-∷ (∈-hd y (flat T ++ flatB r)) (tl⊆ y (inr⊆ (flat T) ⊆-refl))))

mutual
  flat-bdm : ∀ n X → flat (bdm n X) ⊆ flat X
  flat-bdm zero    (node x r) = sing⊆ (∈-hd x (flatB r))
  flat-bdm (suc n) (node x r) = ⊆-∷ (∈-hd x (flatB r)) (tl⊆ x (flatB-bdm n r))

  flatB-bdm : ∀ n r → flatB (bdmB n r) ⊆ flatB r
  flatB-bdm n nil          = ⊆-refl
  flatB-bdm n (cons T y r) =
    ⊆-∷ (∈-hd y (flat T ++ flatB r)) (tl⊆ y (⊆-++-mono (flat-bdm n T) (flatB-bdm n r)))

mutual
  flat-bdp : ∀ n X → flat (bdp n X) ⊆ flat X
  flat-bdp zero    (node x r) = sing⊆ (lastv-∈ x r)
  flat-bdp (suc n) (node x r) = ⊆-∷ (∈-hd x (flatB r)) (tl⊆ x (flatB-bdp n r))

  flatB-bdp : ∀ n r → flatB (bdpB n r) ⊆ flatB r
  flatB-bdp n nil          = ⊆-refl
  flatB-bdp n (cons T y r) =
    ⊆-∷ (∈-hd y (flat T ++ flatB r)) (tl⊆ y (⊆-++-mono (flat-bdp n T) (flatB-bdp n r)))

flatB-++ : ∀ (r₁ r₂ : Br Nat) → flatB (r₁ ++B r₂) ≡ flatB r₁ ++ flatB r₂
flatB-++ nil          r₂ = refl
flatB-++ (cons T y r) r₂ = cong (y ∷_) (trans (cong (flat T ++_) (flatB-++ r r₂)) (sym (++-assoc (flat T) (flatB r) (flatB r₂))))

mutual
  flat-glue : ∀ n X Y → bdp n X ≡ bdm n Y → flat (glue n X Y) ≈ (flat X ++ flat Y)
  flat-glue zero (node x r₁) (node y r₂) e rewrite flatB-++ r₁ r₂ =
    ⊆-∷ (∈-++ˡ x L1 L2 (∈-hd x (flatB r₁))) (⊆-++ (inl⊆ L2 (⊆-tl x (flatB r₁))) (inr⊆ L1 (⊆-tl y (flatB r₂)))) ,
    ⊆-++ (⊆-∷ (∈-hd x (flatB r₁ ++ flatB r₂)) (tl⊆ x (⊆-l (flatB r₁) (flatB r₂))))
         (⊆-∷ ym (tl⊆ x (⊆-r (flatB r₁) (flatB r₂))))
    where
    L1 = x ∷ flatB r₁
    L2 = y ∷ flatB r₂
    G  = x ∷ (flatB r₁ ++ flatB r₂)
    ym : y ∈ G
    ym = subst (λ z → z ∈ G) (node-x e)
           (∈⊆ (lastv-∈ x r₁) (⊆-∷ (∈-hd x (flatB r₁ ++ flatB r₂)) (tl⊆ x (⊆-l (flatB r₁) (flatB r₂)))))
  flat-glue (suc n) (node x r₁) (node y r₂) e with node-x e
  ... | refl =
    let (f , g) = flatB-glue n r₁ r₂ (node-r e)
        R = (x ∷ flatB r₁) ++ (x ∷ flatB r₂)
    in ⊆-∷ (∈-++ˡ x (x ∷ flatB r₁) (x ∷ flatB r₂) (∈-hd x (flatB r₁)))
           (⊆-trans f (⊆-++ (inl⊆ (x ∷ flatB r₂) (⊆-tl x (flatB r₁))) (inr⊆ (x ∷ flatB r₁) (⊆-tl x (flatB r₂))))) ,
       ⊆-++ (⊆-∷ (∈-hd x (flatB (glueB n r₁ r₂))) (tl⊆ x (⊆-trans (⊆-l (flatB r₁) (flatB r₂)) g)))
            (⊆-∷ (∈-hd x (flatB (glueB n r₁ r₂))) (tl⊆ x (⊆-trans (⊆-r (flatB r₁) (flatB r₂)) g)))

  flatB-glue : ∀ n r₁ r₂ → bdpB n r₁ ≡ bdmB n r₂ → flatB (glueB n r₁ r₂) ≈ (flatB r₁ ++ flatB r₂)
  flatB-glue n nil            nil             e = ≈-refl
  flatB-glue n nil            (cons T y r)    ()
  flatB-glue n (cons T y r)   nil             ()
  flatB-glue n (cons T₁ y r₁) (cons T₂ y₂ r₂) e with cons-y e
  ... | refl =
    let (f₁ , g₁) = flat-glue n T₁ T₂ (cons-T e)
        (f₂ , g₂) = flatB-glue n r₁ r₂ (cons-r e)
        L₁ = y ∷ (flat T₁ ++ flatB r₁)
        L₂ = y ∷ (flat T₂ ++ flatB r₂)
        GT = flat (glue n T₁ T₂)
        GB = flatB (glueB n r₁ r₂)
        G  = GT ++ GB
    in ⊆-∷ (∈-++ˡ y L₁ L₂ (∈-hd y (flat T₁ ++ flatB r₁)))
           (⊆-++ (⊆-trans f₁ (⊆-++ (inl⊆ L₂ (tl⊆ y (⊆-l (flat T₁) (flatB r₁)))) (inr⊆ L₁ (tl⊆ y (⊆-l (flat T₂) (flatB r₂))))))
                 (⊆-trans f₂ (⊆-++ (inl⊆ L₂ (tl⊆ y (⊆-r (flat T₁) (flatB r₁)))) (inr⊆ L₁ (tl⊆ y (⊆-r (flat T₂) (flatB r₂))))))) ,
       ⊆-++ (⊆-∷ (∈-hd y G) (tl⊆ y (⊆-++ (inl⊆ GB (⊆-trans (⊆-l (flat T₁) (flat T₂)) g₁))
                                          (inr⊆ GT (⊆-trans (⊆-l (flatB r₁) (flatB r₂)) g₂)))))
            (⊆-∷ (∈-hd y G) (tl⊆ y (⊆-++ (inl⊆ GB (⊆-trans (⊆-r (flat T₁) (flat T₂)) g₁))
                                          (inr⊆ GT (⊆-trans (⊆-r (flatB r₁) (flatB r₂)) g₂)))))

-- The labels of a composite are the labels of its pieces.
mutual
  cp-flat : ∀ {k U X} → P𝒯.Cp k U X → flat X ≈ cmap flat (flat U)
  cp-flat (P𝒯.cp u) = cpB-flat u

  cpB-flat : ∀ {k x r X} → P𝒯.CpB k x r X → flat X ≈ (flat x ++ cmap flat (flatB r))
  cpB-flat {x = x} (P𝒯.cnil _) = ≡→≈ (sym (++-[] (flat x)))
  cpB-flat {k} {x} {cons T y r} (P𝒯.ccons {a = a} {b = b} ca e cb p) rewrite cmap-++ flat (flat T) (flatB r) =
    ⊆-trans fg (⊆-++ (⊆-trans fa (inr⊆ X0 (inr⊆ Y0 (⊆-l CT CR))))
                     (⊆-trans fb (⊆-++ (inr⊆ X0 (⊆-l Y0 (CT ++ CR))) (inr⊆ X0 (inr⊆ Y0 (⊆-r CT CR)))))) ,
    ⊆-++ (⊆-trans (subst (λ z → flat z ⊆ flat a) e (flat-bdm k a)) (⊆-trans (⊆-l A B) gg))
         (⊆-++ (⊆-trans (⊆-l Y0 CR) (⊆-trans gb (⊆-trans (⊆-r A B) gg)))
               (⊆-++ (⊆-trans ga (⊆-trans (⊆-l A B) gg))
                     (⊆-trans (⊆-r Y0 CR) (⊆-trans gb (⊆-trans (⊆-r A B) gg)))))
    where
    A  = flat a
    B  = flat b
    X0 = flat x
    Y0 = flat y
    CT = cmap flat (flat T)
    CR = cmap flat (flatB r)
    fg = fst (flat-glue k a b p)
    gg = snd (flat-glue k a b p)
    fa = fst (cp-flat ca)
    ga = snd (cp-flat ca)
    fb = fst (cpB-flat cb)
    gb = snd (cpB-flat cb)

------------------------------------------------------------------------
-- Discs.

module _ (Θ : Ctx) (ord : ArrOrd Θ) where

  tv-discT : ∀ A U → PsTy A → ∀ w → lookup Θ w ≡ just A → TV Θ ord A U → TV Θ ord ⋆ (discT A U)
  tv-discT ⋆                       U ⋆ₚ        w lw t = t
  tv-discT (arr B (var a) (var b)) U (arrₚ pB) w lw t =
    let (la , lb , _) = ord w B a b lw in
    tv-discT B (node a (cons U b nil)) pB a la (la , t , lb , tt)

flat-discT : ∀ A U → PsTy A → flat (discT A U) ≈ (flat U ++ fvTy A)
flat-discT ⋆                       U ⋆ₚ        = ≡→≈ (sym (++-[] (flat U)))
flat-discT (arr B (var a) (var b)) U (arrₚ pB) =
  let (f , g) = flat-discT B (node a (cons U b nil)) pB
      R  = flat U ++ (fvTy B ++ (a ∷ b ∷ []))
      ab = a ∷ b ∷ []
  in ⊆-trans f (⊆-++ (⊆-∷ (∈-r a ab (∈-hd a (b ∷ [])))
                         (⊆-∷ (∈-r b ab (∈-tl b a (b ∷ []) (∈-hd b [])))
                              (⊆-++ (inl⊆ _ ⊆-refl) ⊆-[])))
                     (inr⊆ (flat U) (⊆-l (fvTy B) ab))) ,
     ⊆-trans (⊆-++ (tl⊆ a (tl⊆ b (inl⊆ [] ⊆-refl)) |> inl⊆ (fvTy B))
                   (⊆-++ (inr⊆ (a ∷ b ∷ (flat U ++ [])) ⊆-refl)
                         (⊆-∷ (∈-++ˡ a (a ∷ b ∷ (flat U ++ [])) (fvTy B) (∈-hd a (b ∷ (flat U ++ []))))
                              (sing⊆ (∈-++ˡ b (a ∷ b ∷ (flat U ++ [])) (fvTy B) (∈-tl b a (b ∷ (flat U ++ [])) (∈-hd b (flat U ++ []))))))))
             g
  where
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  x |> h = h x
  ∈-r : ∀ v ys → v ∈ ys → v ∈ (flat U ++ (fvTy B ++ ys))
  ∈-r v ys m = ∈-++ʳ v (flat U) (fvTy B ++ ys) (∈-++ʳ v (fvTy B) ys m)

flat-disc : ∀ v A → PsTy A → flat (disc v A) ≈ fvTmTy (var v) A
flat-disc v A pA = flat-discT A (node v nil) pA
