------------------------------------------------------------------------
-- Finster–Mimram's boundaries of a pasting context, described
-- pointwise.
--
--   bd⇒ / bd⇐ : Γ ⊢ps z ∶ C →
--     v ∈ ∂⁻ᵢΓ  ⟺  v ∈ Γ, and dim v < i, or dim v = i and v is not
--                  the target of an (i+1)-variable;
--     v ∈ ∂⁺ᵢΓ  ⟺  the same with "source" for "target".
--
-- The proof is by induction on the pasting derivation. In the target
-- case, the pasting step that adds f : x → y with dim x = i removes
-- the last element of ∂⁺ᵢ, and that element is x (`tgt-last` of
-- Strict.PsFacts, with ∂⁺ᵢ free of repetitions).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.BdryChar (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Strict.PsFacts 𝕊
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- The pointwise description.

pickB : Bool → Nat → Nat → Nat
pickB true  s t = s
pickB false s t = t

-- ∂⁻ᵢ for false, ∂⁺ᵢ for true.
bdV : Bool → Nat → Ctx → List Nat
bdV false i Γ = srcVars i Γ
bdV true  i Γ = tgtVars i Γ

-- v is the source (sg = true) or target (sg = false) of an
-- (i+1)-dimensional variable.
Hit : Bool → Nat → Ctx → Nat → Set
Hit sg i Γ v = Σ Nat λ w → Σ Ty λ B → Σ Nat λ s → Σ Nat λ t →
  (lookup Γ w ≡ just (arr B (var s) (var t))) × (dim B ≡ i) × (pickB sg s t ≡ v)

InBd : Bool → Nat → Ctx → Nat → Set
InBd sg i Γ v = T (v <ℕ len Γ) × (T (dimv Γ v <ℕ i) ⊎ ((dimv Γ v ≡ i) × ¬ Hit sg i Γ v))

------------------------------------------------------------------------
-- Small facts.

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  arr-inj : ∀ {A A′ t t′ u u′} → arr A t u ≡ arr A′ t′ u′ → (A ≡ A′) × (t ≡ t′) × (u ≡ u′)
  arr-inj refl = refl , refl , refl

  var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
  var-inj refl = refl

  just≢nothing : ∀ {X : Set} {a : X} → just a ≡ nothing → ⊥
  just≢nothing ()

  nothing≢just : ∀ {X : Set} {a : X} → nothing ≡ just a → ⊥
  nothing≢just ()

  ⋆≢arr : ∀ {B s t} → ⋆ ≡ arr B s t → ⊥
  ⋆≢arr ()

  f≢t : false ≡ true → ⊥
  f≢t ()

  ≡→== : ∀ {a b} → a ≡ b → (a ==ℕ b) ≡ true
  ≡→== {a} refl = ==-refl a

  -- ¬ (i < suc a) gives a < i.
  not-lt-suc : ∀ i a → (i <ℕ suc a) ≡ false → T (a <ℕ i)
  not-lt-suc zero    a       ()
  not-lt-suc (suc i) zero    _ = tt
  not-lt-suc (suc i) (suc a) p = not-lt-suc i a p

  -- ¬ (i < a) and a ≠ i give a < i.
  not-lt-ne : ∀ i a → (i <ℕ a) ≡ false → (a ==ℕ i) ≡ false → T (a <ℕ i)
  not-lt-ne zero    zero    _ ()
  not-lt-ne zero    (suc a) () _
  not-lt-ne (suc i) zero    _ _ = tt
  not-lt-ne (suc i) (suc a) p q = not-lt-ne i a p q

  -- i < suc a gives ¬ (a < i).
  lt-suc-not : ∀ i a → T (i <ℕ suc a) → T (a <ℕ i) → ⊥
  lt-suc-not zero    a       _ ()
  lt-suc-not (suc i) zero    () _
  lt-suc-not (suc i) (suc a) p q = lt-suc-not i a p q

  lt-asym : ∀ a b → T (a <ℕ b) → T (b <ℕ a) → ⊥
  lt-asym zero    zero    () _
  lt-asym zero    (suc b) _ ()
  lt-asym (suc a) zero    () _
  lt-asym (suc a) (suc b) p q = lt-asym a b p q

  lt-suc-lt : ∀ a b → T (suc a <ℕ b) → T (a <ℕ b)
  lt-suc-lt zero    (suc b) _ = tt
  lt-suc-lt (suc a) (suc b) p = lt-suc-lt a b p

  -- a < i gives suc a < i or suc a = i.
  lt-cases : ∀ a i → T (a <ℕ i) → T (suc a <ℕ i) ⊎ (suc a ≡ i)
  lt-cases zero    (suc zero)    _ = inj₂ refl
  lt-cases zero    (suc (suc i)) _ = inj₁ tt
  lt-cases (suc a) (suc i)       p with lt-cases a i p
  ... | inj₁ q = inj₁ q
  ... | inj₂ q = inj₂ (cong suc q)

  lt-ne : ∀ a b → T (a <ℕ b) → a ≡ b → ⊥
  lt-ne a .a p refl = <-irrefl a p

  -- v < suc (suc n): v < n, v = n or v = suc n.
  split3 : ∀ v n → T (v <ℕ suc (suc n)) → T (v <ℕ n) ⊎ ((v ≡ n) ⊎ (v ≡ suc n))
  split3 zero    zero          _ = inj₂ (inj₁ refl)
  split3 (suc zero) zero       _ = inj₂ (inj₂ refl)
  split3 (suc (suc v)) zero    ()
  split3 zero    (suc n)       _ = inj₁ tt
  split3 (suc v) (suc n)       p with split3 v n p
  ... | inj₁ q          = inj₁ q
  ... | inj₂ (inj₁ q)   = inj₂ (inj₁ (cong suc q))
  ... | inj₂ (inj₂ q)   = inj₂ (inj₂ (cong suc q))

  lt-ss : ∀ v n → T (v <ℕ n) → T (v <ℕ suc (suc n))
  lt-ss v n p = <-suc v (suc n) (<-suc v n p)

  ----------------------------------------------------------------------
  -- Membership.

  ∨-l : ∀ {a} b → a ≡ true → (a ∨ b) ≡ true
  ∨-l b refl = refl

  ∨-r : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r true  _ = refl
  ∨-r false p = p

  ∨-cases : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-cases true  b _ = inj₁ refl
  ∨-cases false b p = inj₂ p

  elem-snoc-l : ∀ v xs y → elem v xs ≡ true → elem v (snoc xs y) ≡ true
  elem-snoc-l v xs y p = trans (elem-++ v xs (y ∷ [])) (∨-l (elem v (y ∷ [])) p)

  elem-snoc-r : ∀ xs y → elem y (snoc xs y) ≡ true
  elem-snoc-r xs y = trans (elem-++ y xs (y ∷ [])) (∨-r (elem y xs) (∨-l false (≡→== {y} refl)))

  elem-snoc : ∀ v xs y → elem v (snoc xs y) ≡ true → (elem v xs ≡ true) ⊎ (v ≡ y)
  elem-snoc v xs y p with ∨-cases (elem v xs) _ (trans (sym (elem-++ v xs (y ∷ []))) p)
  ... | inj₁ q = inj₁ q
  ... | inj₂ q with v ==ℕ y in e
  ...   | true  = inj₂ (==→≡ v y e)
  ...   | false = ⊥-elim (f≢t q)

  elem-snoc2 : ∀ v xs a b → elem v (snoc (snoc xs a) b) ≡ true →
               (elem v xs ≡ true) ⊎ ((v ≡ a) ⊎ (v ≡ b))
  elem-snoc2 v xs a b p with elem-snoc v (snoc xs a) b p
  ... | inj₂ q = inj₂ (inj₂ q)
  ... | inj₁ q with elem-snoc v xs a q
  ...   | inj₁ r = inj₁ r
  ...   | inj₂ r = inj₂ (inj₁ r)

  -- In a list without repetitions, an element other than the last one
  -- lies in the rest.
  nodup-last : ∀ xs x → NoDup (snoc xs x) → elem x xs ≡ false
  nodup-last []       x _       = refl
  nodup-last (a ∷ xs) x (p , q) with x ==ℕ a in e
  ... | true  = ⊥-elim (f≢t (trans (sym p) (trans (cong (λ n → elem n (snoc xs x)) (sym (==→≡ x a e)))
                                                   (elem-snoc-r xs x))))
  ... | false = nodup-last xs x q

  elem-false : ∀ v xs → elem v xs ≡ false → elem v xs ≡ true → ⊥
  elem-false v xs p q = f≢t (trans (sym p) q)

------------------------------------------------------------------------
-- One pasting step.

module Ext (Γ : Ctx) (x : Nat) (A : Ty) (lx : lookup Γ x ≡ just A) where

  B = arr A (var x) (var (len Γ))
  Γ′ = Γ ▸ A ▸ B

  x<   : T (x <ℕ len Γ)
  x<   = lookup-< Γ x lx

  lookup-y : lookup Γ′ (len Γ) ≡ just A
  lookup-y = trans (lookup-wk (Γ ▸ A) B (len Γ) (n<suc (len Γ))) (lookup-top Γ A)

  lookup-f : lookup Γ′ (suc (len Γ)) ≡ just B
  lookup-f = lookup-top (Γ ▸ A) B

  dimv-y : dimv Γ′ (len Γ) ≡ dim A
  dimv-y = cong dimM lookup-y

  dimv-f : dimv Γ′ (suc (len Γ)) ≡ suc (dim A)
  dimv-f = cong dimM lookup-f

  hit-old : ∀ {sg i v} → Hit sg i Γ v → Hit sg i Γ′ v
  hit-old (w , B′ , s , t , e , d , p) =
    w , B′ , s , t , trans (lookup-wk₂ Γ A B w (lookup-< Γ w e)) e , d , p

  hit-f : ∀ sg {i} → dim A ≡ i → Hit sg i Γ′ (pickB sg x (len Γ))
  hit-f sg d = suc (len Γ) , A , x , len Γ , lookup-f , d , refl

  hit-split : ∀ {sg i v} → Hit sg i Γ′ v → Hit sg i Γ v ⊎ ((dim A ≡ i) × (pickB sg x (len Γ) ≡ v))
  hit-split {sg} {i} {v} (w , B′ , s , t , e , d , p) with w ==ℕ suc (len Γ) in e₁
  ... | true with arr-inj (just-inj e)
  ...   | refl , q , r rewrite var-inj q | var-inj r = inj₂ (d , p)
  hit-split {sg} {i} {v} (w , B′ , s , t , e , d , p) | false with w ==ℕ len Γ in e₂
  ...   | true  = inj₁ (x , B′ , s , t , trans lx (cong just (just-inj e)) , d , p)
  ...   | false = inj₁ (w , B′ , s , t , e , d , p)

  dimv-old : ∀ v → T (v <ℕ len Γ) → dimv Γ′ v ≡ dimv Γ v
  dimv-old v p = dimv-wk₂ Γ A B v p

  -- Moving a point of Γ between the two contexts.
  lift : ∀ {sg i v} → ¬ ((dim A ≡ i) × (pickB sg x (len Γ) ≡ v)) → InBd sg i Γ v → InBd sg i Γ′ v
  lift {sg} {i} {v} nn (lv , inj₁ q) = lt-ss v (len Γ) lv , inj₁ (subst (λ n → T (n <ℕ i)) (sym (dimv-old v lv)) q)
  lift {sg} {i} {v} nn (lv , inj₂ (q , nh)) =
    lt-ss v (len Γ) lv , inj₂ (trans (dimv-old v lv) q , no)
    where
    no : ¬ Hit sg i Γ′ v
    no h with hit-split h
    ... | inj₁ h′ = nh h′
    ... | inj₂ r  = nn r

  restrict : ∀ {sg i v} → T (v <ℕ len Γ) → InBd sg i Γ′ v → InBd sg i Γ v
  restrict {i = i} {v = v} lv (_ , inj₁ q) = lv , inj₁ (subst (λ n → T (n <ℕ i)) (dimv-old v lv) q)
  restrict {v = v} lv (_ , inj₂ (q , nh)) = lv , inj₂ (trans (sym (dimv-old v lv)) q , λ h → nh (hit-old h))

  -- The three possible new or removed points.
  src-same : ∀ i → (i <ℕ suc (dim A)) ≡ true → srcVars i Γ′ ≡ srcVars i Γ
  src-same i p rewrite p = refl

  src-new : ∀ i → (i <ℕ suc (dim A)) ≡ false → srcVars i Γ′ ≡ snoc (snoc (srcVars i Γ) (len Γ)) (suc (len Γ))
  src-new i p rewrite p = refl

  tgt-same : ∀ i → (i <ℕ dim A) ≡ true → tgtVars i Γ′ ≡ tgtVars i Γ
  tgt-same i p rewrite p = refl

  tgt-swap : ∀ i → (i <ℕ dim A) ≡ false → (dim A ==ℕ i) ≡ true →
             tgtVars i Γ′ ≡ snoc (dropLastᴸ (tgtVars i Γ)) (len Γ)
  tgt-swap i p q rewrite p | q = refl

  tgt-new : ∀ i → (i <ℕ dim A) ≡ false → (dim A ==ℕ i) ≡ false →
            tgtVars i Γ′ ≡ snoc (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))
  tgt-new i p q rewrite p | q = refl

-- Ends of arrows are variables of the context.
hit-lt : ∀ {Γ sg i v} → ArrOrd Γ → Hit sg i Γ v → T (v <ℕ len Γ)
hit-lt {Γ} {true}  o (w , B , s , t , e , d , refl) = lookup-< Γ s (fst (o w B s t e))
hit-lt {Γ} {false} o (w , B , s , t , e , d , refl) = lookup-< Γ t (fst (snd (o w B s t e)))

------------------------------------------------------------------------
-- The point (ε ▸ ⋆).

private
  pt-nohit : ∀ {sg i v} → ¬ Hit sg i (ε ▸ ⋆) v
  pt-nohit (zero  , B , s , t , e , _) = ⋆≢arr (just-inj e)
  pt-nohit (suc w , B , s , t , e , _) = nothing≢just e

  pt-in : ∀ sg i → InBd sg i (ε ▸ ⋆) 0
  pt-in sg zero    = tt , inj₂ (refl , pt-nohit)
  pt-in sg (suc i) = tt , inj₁ tt

  pt-bd : ∀ sg i → bdV sg i (ε ▸ ⋆) ≡ 0 ∷ []
  pt-bd false i = refl
  pt-bd true  i = refl

  elem0 : ∀ v → elem v (0 ∷ []) ≡ true → v ≡ 0
  elem0 zero    _  = refl
  elem0 (suc v) ()

------------------------------------------------------------------------
-- ⇒

bd⇒ : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ sg i v → elem v (bdV sg i Γ) ≡ true → InBd sg i Γ v
bd⇒ pss sg i v p rewrite elem0 v (subst (λ L → elem v L ≡ true) (pt-bd sg i) p) = pt-in sg i
bd⇒ (psd d) sg i v p = bd⇒ d sg i v p
bd⇒ {Γ ▸ A ▸ _} (pse {Γ} {x} {A} d) false i v p = goal
  where
  F = ps-facts d
  open Ext Γ x A (dang F)
  nn : ∀ {v} → T (v <ℕ len Γ) → ¬ ((dim A ≡ i) × (pickB false x (len Γ) ≡ v))
  nn lv (_ , q) = lt-ne _ _ lv (sym q)
  goal : InBd false i Γ′ v
  split : ∀ b → (i <ℕ suc (dim A)) ≡ b → InBd false i Γ′ v
  goal = split (i <ℕ suc (dim A)) refl
  split true e = let r = bd⇒ d false i v (subst (λ L → elem v L ≡ true) (src-same i e) p)
                in lift (nn (fst r)) r
  split false e with elem-snoc2 v (srcVars i Γ) (len Γ) (suc (len Γ)) (subst (λ L → elem v L ≡ true) (src-new i e) p)
  ...   | inj₁ q = let r = bd⇒ d false i v q in lift (nn (fst r)) r
  ...   | inj₂ (inj₁ refl) =
          <-suc (len Γ) (suc (len Γ)) (n<suc (len Γ)) , inj₁ (subst (λ n → T (n <ℕ i)) (sym dimv-y) (not-lt-suc i (dim A) e))
  ...   | inj₂ (inj₂ refl) = n<suc (suc (len Γ)) , fdim
    where
    fdim : T (dimv Γ′ (suc (len Γ)) <ℕ i) ⊎ ((dimv Γ′ (suc (len Γ)) ≡ i) × ¬ Hit false i Γ′ (suc (len Γ)))
    fdim rewrite dimv-f with lt-cases (dim A) i (not-lt-suc i (dim A) e)
    ... | inj₁ q = inj₁ q
    ... | inj₂ q = inj₂ (q , no)
      where
      no : ¬ Hit false i Γ′ (suc (len Γ))
      no h with hit-split h
      ... | inj₁ h′ = <-irrefl (suc (len Γ)) (<-suc (suc (len Γ)) (len Γ) (hit-lt {Γ} (ord F) h′))
      ... | inj₂ (dA , _) = lt-ne (dim A) i (not-lt-suc i (dim A) e) dA
bd⇒ {Γ ▸ A ▸ _} (pse {Γ} {x} {A} d) true i v p = goal
  where
  F = ps-facts d
  open Ext Γ x A (dang F)
  goal : InBd true i Γ′ v
  split2 : (i <ℕ dim A) ≡ false → ∀ b → (dim A ==ℕ i) ≡ b → InBd true i Γ′ v
  split1 : ∀ b → (i <ℕ dim A) ≡ b → InBd true i Γ′ v
  goal = split1 (i <ℕ dim A) refl
  split1 true e₁ = lift nn r
    where
    r = bd⇒ d true i v (subst (λ L → elem v L ≡ true) (tgt-same i e₁) p)
    nn : ¬ ((dim A ≡ i) × (x ≡ v))
    nn (dA , _) = lt-ne i (dim A) (≡→T e₁) (sym dA)
  split1 false e₁ = split2 e₁ (dim A ==ℕ i) refl
  split2 e₁ true e₂ = swap (elem-snoc v (dropLastᴸ old) (len Γ) (subst (λ L → elem v L ≡ true) (tgt-swap i e₁ e₂) p))
    where
    old = tgtVars i Γ
    dA : dim A ≡ i
    dA = ==→≡ (dim A) i e₂
    last : lastL old ≡ just x
    last = trans (tgt-last d i (subst (λ n → T (n <ℕ suc (dim A))) dA (n<suc (dim A))))
                 (cong just (ti-x e₂))
      where
      ti-x : (dim A ==ℕ i) ≡ true → ti i x A ≡ x
      ti-x q rewrite q = refl
    old≡ : old ≡ snoc (dropLastᴸ old) x
    old≡ = lastL-split old x last
    nd : NoDup (snoc (dropLastᴸ old) x)
    nd = subst NoDup old≡ (tgt-nodup i Γ)
    swap : (elem v (dropLastᴸ old) ≡ true) ⊎ (v ≡ len Γ) → InBd true i Γ′ v
    swap (inj₁ q) = lift nn r
      where
      inOld : elem v old ≡ true
      inOld = subst (λ L → elem v L ≡ true) (sym old≡) (elem-snoc-l v (dropLastᴸ old) x q)
      r = bd⇒ d true i v inOld
      nn : ¬ ((dim A ≡ i) × (x ≡ v))
      nn (_ , refl) = elem-false x (dropLastᴸ old) (nodup-last (dropLastᴸ old) x nd) q
    swap (inj₂ refl) =
      <-suc (len Γ) (suc (len Γ)) (n<suc (len Γ)) , inj₂ (trans dimv-y dA , no)
      where
      no : ¬ Hit true i Γ′ (len Γ)
      no h with hit-split h
      ... | inj₁ h′ = <-irrefl (len Γ) (hit-lt {Γ} (ord F) h′)
      ... | inj₂ (_ , q) = <-irrefl (len Γ) (subst (λ n → T (n <ℕ len Γ)) q x<)
  split2 e₁ false e₂ with elem-snoc2 v (tgtVars i Γ) (len Γ) (suc (len Γ)) (subst (λ L → elem v L ≡ true) (tgt-new i e₁ e₂) p)
  ...     | inj₁ q = lift nn (bd⇒ d true i v q)
    where
    nn : ¬ ((dim A ≡ i) × (x ≡ v))
    nn (dA , _) = f≢t (trans (sym e₂) (≡→== dA))
  ...     | inj₂ (inj₁ refl) =
    <-suc (len Γ) (suc (len Γ)) (n<suc (len Γ)) , inj₁ (subst (λ n → T (n <ℕ i)) (sym dimv-y) (not-lt-ne i (dim A) e₁ e₂))
  ...     | inj₂ (inj₂ refl) = n<suc (suc (len Γ)) , fdim
    where
    fdim : T (dimv Γ′ (suc (len Γ)) <ℕ i) ⊎ ((dimv Γ′ (suc (len Γ)) ≡ i) × ¬ Hit true i Γ′ (suc (len Γ)))
    fdim rewrite dimv-f with lt-cases (dim A) i (not-lt-ne i (dim A) e₁ e₂)
    ... | inj₁ q = inj₁ q
    ... | inj₂ q = inj₂ (q , no)
      where
      no : ¬ Hit true i Γ′ (suc (len Γ))
      no h with hit-split h
      ... | inj₁ h′ = <-irrefl (suc (len Γ)) (<-suc (suc (len Γ)) (len Γ) (hit-lt {Γ} (ord F) h′))
      ... | inj₂ (dA , _) = f≢t (trans (sym e₂) (≡→== dA))

------------------------------------------------------------------------
-- ⇐

private
  sub-elem : ∀ {v L L′} → L ≡ L′ → elem v L ≡ true → elem v L′ ≡ true
  sub-elem {v} q p = subst (λ L → elem v L ≡ true) q p

  elem-ss-old : ∀ v xs a b → elem v xs ≡ true → elem v (snoc (snoc xs a) b) ≡ true
  elem-ss-old v xs a b p = elem-snoc-l v (snoc xs a) b (elem-snoc-l v xs a p)

  elem-ss-a : ∀ xs a b → elem a (snoc (snoc xs a) b) ≡ true
  elem-ss-a xs a b = elem-snoc-l a (snoc xs a) b (elem-snoc-r xs a)

bd⇐ : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ sg i v → InBd sg i Γ v → elem v (bdV sg i Γ) ≡ true
bd⇐ pss false i zero    _ = refl
bd⇐ pss true  i zero    _ = refl
bd⇐ pss sg    i (suc v) (() , _)
bd⇐ (psd d) sg i v p = bd⇐ d sg i v p
bd⇐ {Γ ▸ A ▸ _} (pse {Γ} {x} {A} d) false i v (lv , q) = split (i <ℕ suc (dim A)) refl
  where
  F = ps-facts d
  open Ext Γ x A (dang F)
  split : ∀ b → (i <ℕ suc (dim A)) ≡ b → elem v (srcVars i Γ′) ≡ true
  split true e with split3 v (len Γ) lv
  ... | inj₁ l = sub-elem (sym (src-same i e)) (bd⇐ d false i v (restrict l (lv , q)))
  ... | inj₂ (inj₁ refl) = ⊥-elim (bad q)
    where
    bad : T (dimv Γ′ (len Γ) <ℕ i) ⊎ ((dimv Γ′ (len Γ) ≡ i) × ¬ Hit false i Γ′ (len Γ)) → ⊥
    bad (inj₁ r) = lt-suc-not i (dim A) (≡→T e) (subst (λ n → T (n <ℕ i)) dimv-y r)
    bad (inj₂ (r , nh)) = nh (hit-f false (trans (sym dimv-y) r))
  ... | inj₂ (inj₂ refl) = ⊥-elim (bad q)
    where
    bad : T (dimv Γ′ (suc (len Γ)) <ℕ i) ⊎ ((dimv Γ′ (suc (len Γ)) ≡ i) × ¬ Hit false i Γ′ (suc (len Γ))) → ⊥
    bad (inj₁ r) = lt-suc-not i (dim A) (≡→T e) (lt-suc-lt (dim A) i (subst (λ n → T (n <ℕ i)) dimv-f r))
    bad (inj₂ (r , _)) = <-irrefl (suc (dim A))
      (subst (λ n → T (n <ℕ suc (dim A))) (sym (trans (sym dimv-f) r)) (≡→T e))
  split false e with split3 v (len Γ) lv
  ... | inj₁ l = sub-elem (sym (src-new i e)) (elem-ss-old v (srcVars i Γ) (len Γ) (suc (len Γ)) (bd⇐ d false i v (restrict l (lv , q))))
  ... | inj₂ (inj₁ refl) = sub-elem (sym (src-new i e)) (elem-ss-a (srcVars i Γ) (len Γ) (suc (len Γ)))
  ... | inj₂ (inj₂ refl) = sub-elem (sym (src-new i e)) (elem-snoc-r (snoc (srcVars i Γ) (len Γ)) (suc (len Γ)))
bd⇐ {Γ ▸ A ▸ _} (pse {Γ} {x} {A} d) true i v (lv , q) = split1 (i <ℕ dim A) refl
  where
  F = ps-facts d
  open Ext Γ x A (dang F)
  split2 : (i <ℕ dim A) ≡ false → ∀ b → (dim A ==ℕ i) ≡ b → elem v (tgtVars i Γ′) ≡ true
  split1 : ∀ b → (i <ℕ dim A) ≡ b → elem v (tgtVars i Γ′) ≡ true
  split1 true e₁ with split3 v (len Γ) lv
  ... | inj₁ l = sub-elem (sym (tgt-same i e₁)) (bd⇐ d true i v (restrict l (lv , q)))
  ... | inj₂ (inj₁ refl) = ⊥-elim (bad q)
    where
    bad : T (dimv Γ′ (len Γ) <ℕ i) ⊎ ((dimv Γ′ (len Γ) ≡ i) × ¬ Hit true i Γ′ (len Γ)) → ⊥
    bad (inj₁ r) = lt-asym i (dim A) (≡→T e₁) (subst (λ n → T (n <ℕ i)) dimv-y r)
    bad (inj₂ (r , _)) = lt-ne i (dim A) (≡→T e₁) (sym (trans (sym dimv-y) r))
  ... | inj₂ (inj₂ refl) = ⊥-elim (bad q)
    where
    bad : T (dimv Γ′ (suc (len Γ)) <ℕ i) ⊎ ((dimv Γ′ (suc (len Γ)) ≡ i) × ¬ Hit true i Γ′ (suc (len Γ))) → ⊥
    bad (inj₁ r) = lt-asym i (dim A) (≡→T e₁) (lt-suc-lt (dim A) i (subst (λ n → T (n <ℕ i)) dimv-f r))
    bad (inj₂ (r , _)) = lt-asym i (dim A) (≡→T e₁)
      (subst (λ n → T (dim A <ℕ n)) (trans (sym dimv-f) r) (n<suc (dim A)))
  split1 false e₁ = split2 e₁ (dim A ==ℕ i) refl
  split2 e₁ true e₂ with split3 v (len Γ) lv
  ... | inj₁ l = sub-elem (sym (tgt-swap i e₁ e₂)) (elem-snoc-l v (dropLastᴸ old) (len Γ) inD)
    where
    old = tgtVars i Γ
    dA : dim A ≡ i
    dA = ==→≡ (dim A) i e₂
    last : lastL old ≡ just x
    last = trans (tgt-last d i (subst (λ n → T (n <ℕ suc (dim A))) dA (n<suc (dim A))))
                 (cong just (ti-x e₂))
      where
      ti-x : (dim A ==ℕ i) ≡ true → ti i x A ≡ x
      ti-x r rewrite r = refl
    old≡ : old ≡ snoc (dropLastᴸ old) x
    old≡ = lastL-split old x last
    inOld : elem v (snoc (dropLastᴸ old) x) ≡ true
    inOld = sub-elem old≡ (bd⇐ d true i v (restrict l (lv , q)))
    nox : T (dimv Γ′ x <ℕ i) ⊎ ((dimv Γ′ x ≡ i) × ¬ Hit true i Γ′ x) → ⊥
    nox (inj₁ r) = <-irrefl i (subst (λ n → T (n <ℕ i)) (trans (dimv-old x x<) (trans (cong dimM (dang F)) dA)) r)
    nox (inj₂ (_ , nh)) = nh (hit-f true dA)
    notx : v ≡ x → ⊥
    notx r = nox (subst (λ n → T (dimv Γ′ n <ℕ i) ⊎ ((dimv Γ′ n ≡ i) × ¬ Hit true i Γ′ n)) r q)
    inD : elem v (dropLastᴸ old) ≡ true
    inD with elem-snoc v (dropLastᴸ old) x inOld
    ... | inj₁ r = r
    ... | inj₂ r = ⊥-elim (notx r)
  ... | inj₂ (inj₁ refl) = sub-elem (sym (tgt-swap i e₁ e₂)) (elem-snoc-r (dropLastᴸ (tgtVars i Γ)) (len Γ))
  ... | inj₂ (inj₂ refl) = ⊥-elim (bad q)
    where
    dA : dim A ≡ i
    dA = ==→≡ (dim A) i e₂
    bad : T (dimv Γ′ (suc (len Γ)) <ℕ i) ⊎ ((dimv Γ′ (suc (len Γ)) ≡ i) × ¬ Hit true i Γ′ (suc (len Γ))) → ⊥
    bad (inj₁ r) = <-irrefl i (lt-suc-lt i i (subst (λ n → T (n <ℕ i)) (trans dimv-f (cong suc dA)) r))
    bad (inj₂ (r , _)) = <-irrefl i (subst (λ n → T (i <ℕ n)) (trans (sym (cong suc dA)) (trans (sym dimv-f) r)) (n<suc i))
  split2 e₁ false e₂ with split3 v (len Γ) lv
  ... | inj₁ l = sub-elem (sym (tgt-new i e₁ e₂)) (elem-ss-old v (tgtVars i Γ) (len Γ) (suc (len Γ)) (bd⇐ d true i v (restrict l (lv , q))))
  ... | inj₂ (inj₁ refl) = sub-elem (sym (tgt-new i e₁ e₂)) (elem-ss-a (tgtVars i Γ) (len Γ) (suc (len Γ)))
  ... | inj₂ (inj₂ refl) = sub-elem (sym (tgt-new i e₁ e₂)) (elem-snoc-r (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ)))
