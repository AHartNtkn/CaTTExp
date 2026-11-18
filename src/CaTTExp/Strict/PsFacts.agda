------------------------------------------------------------------------
-- Combinatorics of pasting contexts needed for strict-model soundness
-- (ledger item A3a).
--
--  * ordering: in a pasting context every arrow f : x → y has x < y
--    (de Bruijn levels), and its endpoints have the arrow's base type;
--  * the last element of ∂⁺ᵢ is the i-dimensional target of the
--    dangling cell (Finster–Mimram's construction of ∂⁺);
--  * the boundary formula: for i + 1 ≥ dim Γ, writing W for the
--    (i+1)-variables and S∓ for the i-variables of ∂∓ᵢΓ,
--        ∂⁺W + S⁻ = ∂⁻W + S⁺        (as bags),
--    i.e. ∂W = S⁺ − S⁻ in the chain complex λΓ;
--  * ∂∓ᵢΓ has no repeated variables, and ∂⁻ᵢΓ contains a variable of
--    dimension i when i ≤ dim Γ.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Strict.PsFacts (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ; ps-ty)
open import CaTTExp.Strict.Bag

------------------------------------------------------------------------
-- Natural numbers.

≡→T : ∀ {b} → b ≡ true → T b
≡→T refl = tt

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true} _ = refl

==-refl : ∀ n → (n ==ℕ n) ≡ true
==-refl zero    = refl
==-refl (suc n) = ==-refl n

==→≡ : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
==→≡ m n p = ==ℕ-sound m n (≡→T p)

<-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
<-suc zero    (suc n) _ = tt
<-suc (suc i) (suc n) p = <-suc i n p

n<suc : ∀ n → T (n <ℕ suc n)
n<suc zero    = tt
n<suc (suc n) = n<suc n

<→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
<→≢ zero    (suc n) _ = refl
<→≢ (suc i) (suc n) p = <→≢ i n p

<→≢′ : ∀ i n → T (i <ℕ n) → (n ==ℕ i) ≡ false
<→≢′ zero    (suc n) _ = refl
<→≢′ (suc i) (suc n) p = <→≢′ i n p

<-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans zero    (suc b) (suc c) _ _ = tt
<-trans (suc a) (suc b) (suc c) p q = <-trans a b c p q

<-irrefl : ∀ n → T (n <ℕ n) → ⊥
<-irrefl zero    ()
<-irrefl (suc n) p = <-irrefl n p

-- a < suc b  and  a ≠ b  give  a < b
<suc-≢ : ∀ a b → T (a <ℕ suc b) → (a ==ℕ b) ≡ false → T (a <ℕ b)
<suc-≢ zero    zero    _ ()
<suc-≢ zero    (suc b) _ _ = tt
<suc-≢ (suc a) zero    p _ = ⊥-elim (z a p)
  where
  z : ∀ a → T (suc a <ℕ 1) → ⊥
  z zero    ()
  z (suc a) ()
<suc-≢ (suc a) (suc b) p q = <suc-≢ a b p q

max-≤ˡ : ∀ a b c → T (max a b <ℕ c) → T (a <ℕ c)
max-≤ˡ zero    b       (suc c) _ = tt
max-≤ˡ (suc a) zero    c       p = p
max-≤ˡ (suc a) (suc b) (suc c) p = max-≤ˡ a b c p

max-≤ʳ : ∀ a b c → T (max a b <ℕ c) → T (b <ℕ c)
max-≤ʳ zero    b       c       p = p
max-≤ʳ (suc a) zero    (suc c) _ = tt
max-≤ʳ (suc a) (suc b) (suc c) p = max-≤ʳ a b c p

≤-max : ∀ a b c → T (a <ℕ c) → T (b <ℕ c) → T (max a b <ℕ c)
≤-max zero    b       c       _ q = q
≤-max (suc a) zero    c       p _ = p
≤-max (suc a) (suc b) (suc c) p q = ≤-max a b c p q

------------------------------------------------------------------------
-- Lookup.

lookup-top : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
lookup-top Γ A rewrite ==-refl (len Γ) = refl

lookup-wk : ∀ Γ B v → T (v <ℕ len Γ) → lookup (Γ ▸ B) v ≡ lookup Γ v
lookup-wk Γ B v p rewrite <→≢ v (len Γ) p = refl

lookup-< : ∀ Γ v {A} → lookup Γ v ≡ just A → T (v <ℕ len Γ)
lookup-< (Γ ▸ B) v eq with v ==ℕ len Γ in e
... | true  rewrite ==→≡ v (len Γ) e = n<suc (len Γ)
... | false = <-suc v (len Γ) (lookup-< Γ v eq)

lookup-wk₂ : ∀ Γ A B v → T (v <ℕ len Γ) → lookup (Γ ▸ A ▸ B) v ≡ lookup Γ v
lookup-wk₂ Γ A B v p =
  trans (lookup-wk (Γ ▸ A) B v (<-suc v (len Γ) p)) (lookup-wk Γ A v p)

dimM : Maybe Ty → Nat
dimM (just A) = dim A
dimM nothing  = 0

dimv : Ctx → Nat → Nat
dimv Γ v = dimM (lookup Γ v)

------------------------------------------------------------------------
-- Ordering and the shape of types in a pasting context.

ArrOrd : Ctx → Set
ArrOrd Γ = ∀ f A x y → lookup Γ f ≡ just (arr A (var x) (var y)) →
           (lookup Γ x ≡ just A) × (lookup Γ y ≡ just A) × T (x <ℕ y)

-- Every type of a pasting context has variable endpoints.
PsCtx : Ctx → Set
PsCtx Γ = ∀ f A → lookup Γ f ≡ just A → PsTy A

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  arr-inj : ∀ {A A′ t t′ u u′} → arr A t u ≡ arr A′ t′ u′ → (A ≡ A′) × (t ≡ t′) × (u ≡ u′)
  arr-inj refl = refl , refl , refl

  var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
  var-inj refl = refl

-- Facts carried along a pasting derivation: the dangling cell z : C is
-- a variable of type C, and C (if an arrow) is ordered.
record PsFacts (Γ : Ctx) (z : Nat) (C : Ty) : Set where
  field
    dang  : lookup Γ z ≡ just C
    ord   : ArrOrd Γ
    shape : PsCtx Γ

open PsFacts public

ps-facts : ∀ {Γ z C} → Γ ⊢ps z ∶ C → PsFacts Γ z C
ps-facts pss = record { dang = refl ; ord = o ; shape = s }
  where
  o : ArrOrd (ε ▸ ⋆)
  o zero A x y ()
  o (suc f) A x y ()
  s : PsCtx (ε ▸ ⋆)
  s zero A eq rewrite sym (just-inj eq) = ⋆ₚ
  s (suc f) A ()
ps-facts (psd {f = f} {A} {x} {y} d) =
  let F = ps-facts d in
  record { dang = fst (snd (ord F f A x y (dang F))) ; ord = ord F ; shape = shape F }
ps-facts {Γ ▸ A ▸ B} (pse {Γ} {x} {A} d) =
  record { dang = lookup-top (Γ ▸ A) B ; ord = o ; shape = s }
  where
  F = ps-facts d
  lx : T (x <ℕ len Γ)
  lx = lookup-< Γ x (dang F)

  o : ArrOrd (Γ ▸ A ▸ B)
  o f A′ a b eq with f ==ℕ suc (len Γ) in e₁
  ... | true =
    let (p , q , r) = arr-inj (just-inj eq) in
    subst (λ X → lookup (Γ ▸ A ▸ B) a ≡ just X) p
      (subst (λ n → lookup (Γ ▸ A ▸ B) n ≡ just A) (var-inj q)
        (trans (lookup-wk₂ Γ A B x lx) (dang F))) ,
    subst (λ X → lookup (Γ ▸ A ▸ B) b ≡ just X) p
      (subst (λ n → lookup (Γ ▸ A ▸ B) n ≡ just A) (var-inj r)
        (trans (lookup-wk (Γ ▸ A) B (len Γ) (n<suc (len Γ))) (lookup-top Γ A))) ,
    subst₂ (λ m n → T (m <ℕ n)) (var-inj q) (var-inj r) lx
    where
    subst₂ : ∀ {X : Set} (P : X → X → Set) {a b c d} → a ≡ b → c ≡ d → P a c → P b d
    subst₂ P refl refl p = p
  ... | false with f ==ℕ len Γ in e₂
  ...   | true =
    -- f is the copy y : A of the dangling x : A.
    let eqA = just-inj eq
        (lx′ , ly′ , o′) = ord F x A′ a b (trans (dang F) (cong just eqA))
    in wk a lx′ , wk b ly′ , o′
    where
    wk : ∀ n {X} → lookup Γ n ≡ just X → lookup (Γ ▸ A ▸ B) n ≡ just X
    wk n p = trans (lookup-wk₂ Γ A B n (lookup-< Γ n p)) p
  ...   | false =
    let (lx′ , ly′ , o′) = ord F f A′ a b eq
    in wk a lx′ , wk b ly′ , o′
    where
    wk : ∀ n {X} → lookup Γ n ≡ just X → lookup (Γ ▸ A ▸ B) n ≡ just X
    wk n p = trans (lookup-wk₂ Γ A B n (lookup-< Γ n p)) p

  s : PsCtx (Γ ▸ A ▸ B)
  s f A′ eq with f ==ℕ suc (len Γ) in e₁
  ... | true  rewrite sym (just-inj eq) = arrₚ (ps-ty d)
  ... | false with f ==ℕ len Γ in e₂
  ...   | true  rewrite sym (just-inj eq) = ps-ty d
  ...   | false = shape F f A′ eq

------------------------------------------------------------------------
-- The last element of ∂⁺ᵢ is the i-dimensional target of the dangling
-- cell.

lastL : List Nat → Maybe Nat
lastL []           = nothing
lastL (x ∷ [])     = just x
lastL (x ∷ y ∷ xs) = lastL (y ∷ xs)

mutual
  -- ti i z C: iterate "target" from z : C down to dimension i.
  ti : Nat → Nat → Ty → Nat
  ti i z C = if dim C ==ℕ i then z else tiT i z C

  tiT : Nat → Nat → Ty → Nat
  tiT i z (arr A _ (var y)) = ti i y A
  tiT i z _                 = z

lastL-snoc : ∀ xs y → lastL (snoc xs y) ≡ just y
lastL-snoc []            y = refl
lastL-snoc (x ∷ [])      y = refl
lastL-snoc (x ∷ x′ ∷ xs) y = lastL-snoc (x′ ∷ xs) y

lastL-split : ∀ xs x → lastL xs ≡ just x → xs ≡ snoc (dropLastᴸ xs) x
lastL-split []           x ()
lastL-split (a ∷ [])     x p = cong (_∷ []) (just-inj p)
lastL-split (a ∷ b ∷ xs) x p = cong (a ∷_) (lastL-split (b ∷ xs) x p)

private
  -- i < suc (suc a), ¬ (i < a), a ≠ i  give  suc a = i
  third : ∀ i a → T (i <ℕ suc (suc a)) → (i <ℕ a) ≡ false → (a ==ℕ i) ≡ false → (suc a ==ℕ i) ≡ true
  third zero    zero    _ _ ()
  third zero    (suc a) _ () _
  third (suc zero) zero _ _ _ = refl
  third (suc (suc i)) zero p _ _ = ⊥-elim (z i p)
    where
    z : ∀ i → T (suc (suc i) <ℕ 2) → ⊥
    z zero    ()
    z (suc i) ()
  third (suc i) (suc a) p q r = third i a p q r

  lt-false : ∀ i a → T (i <ℕ a) → (a ==ℕ i) ≡ false
  lt-false = λ i a p → <→≢′ i a p

  lt-suc-false : ∀ i a → T (i <ℕ suc a) → (suc a ==ℕ i) ≡ false
  lt-suc-false i a p = <→≢′ i (suc a) p

tgt-last : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i → T (i <ℕ suc (dim C)) → lastL (tgtVars i Γ) ≡ just (ti i z C)
tgt-last pss zero _ = refl
tgt-last pss (suc i) ()
tgt-last (psd {f = f} {A} {x} {y} d) i p
  with tgt-last d i (<-suc i (suc (dim A)) p)
... | ih rewrite lt-suc-false i (dim A) p = ih
tgt-last (pse {Γ} {x} {A} d) i p with i <ℕ dim A in e₁
... | true
  rewrite lt-suc-false i (dim A) (<-trans i (dim A) (suc (dim A)) (≡→T e₁) (n<suc (dim A)))
        | <→≢′ i (dim A) (≡→T e₁) =
  trans (tgt-last d i (<-suc i (dim A) (≡→T e₁))) (cong just (same (ps-ty d) (≡→T e₁)))
  where
  same : ∀ {A} → PsTy A → T (i <ℕ dim A) → ti i x A ≡ tiT i (len Γ) A
  same ⋆ₚ ()
  same {arr B (var a) (var b)} (arrₚ _) q rewrite <→≢′ i (dim (arr B (var a) (var b))) q = refl
... | false with dim A ==ℕ i in e₂
...   | true rewrite ==→≡ (dim A) i e₂ | lt-suc-false i i (n<suc i) =
  lastL-snoc (dropLastᴸ (tgtVars i Γ)) (len Γ)
...   | false rewrite third i (dim A) p e₁ e₂ = lastL-snoc (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))

------------------------------------------------------------------------
-- Bounds: every variable of ∂∓ᵢΓ is a variable of Γ.

Below : Nat → List Nat → Set
Below n []       = ⊤
Below n (x ∷ xs) = T (x <ℕ n) × Below n xs

Below-suc : ∀ n xs → Below n xs → Below (suc n) xs
Below-suc n []       _       = tt
Below-suc n (x ∷ xs) (p , q) = <-suc x n p , Below-suc n xs q

Below-++ : ∀ n xs ys → Below n xs → Below n ys → Below n (xs ++ ys)
Below-++ n []       ys _       q = q
Below-++ n (x ∷ xs) ys (p , r) q = p , Below-++ n xs ys r q

Below-dropLast : ∀ n xs → Below n xs → Below n (dropLastᴸ xs)
Below-dropLast n []           _       = tt
Below-dropLast n (x ∷ [])     _       = tt
Below-dropLast n (x ∷ y ∷ xs) (p , q) = p , Below-dropLast n (y ∷ xs) q

Below-downFrom : ∀ n → Below n (downFrom n)
Below-downFrom zero    = tt
Below-downFrom (suc n) = n<suc n , Below-suc n (downFrom n) (Below-downFrom n)

private
  Below-new : ∀ n xs → Below n xs → Below (suc (suc n)) (snoc (snoc xs n) (suc n))
  Below-new n xs p =
    Below-++ (suc (suc n)) (snoc xs n) (suc n ∷ [])
      (Below-++ (suc (suc n)) xs (n ∷ [])
        (Below-suc (suc n) xs (Below-suc n xs p)) (<-suc n (suc n) (n<suc n) , tt))
      (n<suc (suc n) , tt)

src-below : ∀ i Γ → Below (len Γ) (srcVars i Γ)
src-below i ε               = tt
src-below i (ε ▸ _)         = tt , tt
src-below i (Γ ▸ A ▸ B) with i <ℕ suc (dim A)
... | true  = Below-suc (suc (len Γ)) _ (Below-suc (len Γ) _ (src-below i Γ))
... | false = Below-new (len Γ) _ (src-below i Γ)

tgt-below : ∀ i Γ → Below (len Γ) (tgtVars i Γ)
tgt-below i ε               = tt
tgt-below i (ε ▸ _)         = tt , tt
tgt-below i (Γ ▸ A ▸ B) with i <ℕ dim A
... | true  = Below-suc (suc (len Γ)) _ (Below-suc (len Γ) _ (tgt-below i Γ))
... | false with dim A ==ℕ i
...   | true  =
  Below-++ (suc (suc (len Γ))) (dropLastᴸ (tgtVars i Γ)) (len Γ ∷ [])
    (Below-suc (suc (len Γ)) _ (Below-suc (len Γ) _
      (Below-dropLast (len Γ) _ (tgt-below i Γ))))
    (<-suc (len Γ) (suc (len Γ)) (n<suc (len Γ)) , tt)
...   | false = Below-new (len Γ) _ (tgt-below i Γ)

------------------------------------------------------------------------
-- The chain complex λΓ: one basis element (v) per variable v, of
-- degree dim v; an arrow f : x → y has ∂⁺f = y and ∂⁻f = x.

tup : Nat → Tuple
tup v = v ∷ []

∂T : Bool → Maybe Ty → Bag
∂T b (just (arr _ (var x) (var y))) = tup (if b then y else x) ∷ []
∂T b _                              = []

∂λ : Ctx → Bool → Tuple → Bag
∂λ Γ b (v ∷ []) = ∂T b (lookup Γ v)
∂λ Γ b _        = []

-- The basis elements of degree k among a list of variables.
sel : Ctx → Nat → List Nat → Bag
sel Γ k []       = []
sel Γ k (v ∷ vs) = if dimv Γ v ==ℕ k then tup v ∷ sel Γ k vs else sel Γ k vs

-- All variables of degree k.
Wb : Ctx → Nat → Bag
Wb Γ k = sel Γ k (varsCtx Γ)

sel-++ : ∀ Γ k xs ys → sel Γ k (xs ++ ys) ≡ sel Γ k xs ++ sel Γ k ys
sel-++ Γ k []       ys = refl
sel-++ Γ k (v ∷ xs) ys with dimv Γ v ==ℕ k
... | true  = cong (tup v ∷_) (sel-++ Γ k xs ys)
... | false = sel-++ Γ k xs ys

sel-hit : ∀ Γ k v vs → dimv Γ v ≡ k → sel Γ k (v ∷ vs) ≡ tup v ∷ sel Γ k vs
sel-hit Γ k v vs p rewrite p | ==-refl k = refl

sel-miss : ∀ Γ k v vs → (dimv Γ v ==ℕ k) ≡ false → sel Γ k (v ∷ vs) ≡ sel Γ k vs
sel-miss Γ k v vs p rewrite p = refl

dimv-wk : ∀ Γ B v → T (v <ℕ len Γ) → dimv (Γ ▸ B) v ≡ dimv Γ v
dimv-wk Γ B v p = cong dimM (lookup-wk Γ B v p)

sel-ext : ∀ Γ B k vs → Below (len Γ) vs → sel (Γ ▸ B) k vs ≡ sel Γ k vs
sel-ext Γ B k []       _       = refl
sel-ext Γ B k (v ∷ vs) (p , q) rewrite dimv-wk Γ B v p with dimv Γ v ==ℕ k
... | true  = cong (tup v ∷_) (sel-ext Γ B k vs q)
... | false = sel-ext Γ B k vs q

∂-ext : ∀ Γ B b Δ k vs → Below (len Γ) vs →
        cm (∂λ (Γ ▸ B) b) (sel Δ k vs) ≡ cm (∂λ Γ b) (sel Δ k vs)
∂-ext Γ B b Δ k []       _       = refl
∂-ext Γ B b Δ k (v ∷ vs) (p , q) with dimv Δ v ==ℕ k
... | true  rewrite lookup-wk Γ B v p = cong (∂T b (lookup Γ v) ++_) (∂-ext Γ B b Δ k vs q)
... | false = ∂-ext Γ B b Δ k vs q

sel-ext₂ : ∀ Γ A B k vs → Below (len Γ) vs → sel (Γ ▸ A ▸ B) k vs ≡ sel Γ k vs
sel-ext₂ Γ A B k vs p =
  trans (sel-ext (Γ ▸ A) B k vs (Below-suc (len Γ) vs p)) (sel-ext Γ A k vs p)

-- ∂ on the degree-k variables of a list, after a two-step extension.
∂-ext₂ : ∀ Γ A B b k vs → Below (len Γ) vs →
         cm (∂λ (Γ ▸ A ▸ B) b) (sel (Γ ▸ A ▸ B) k vs) ≡ cm (∂λ Γ b) (sel Γ k vs)
∂-ext₂ Γ A B b k vs p =
  trans (cong (cm (∂λ (Γ ▸ A ▸ B) b)) (sel-ext₂ Γ A B k vs p))
 (trans (∂-ext (Γ ▸ A) B b Γ k vs (Below-suc (len Γ) vs p))
        (∂-ext Γ A b Γ k vs p))

------------------------------------------------------------------------
-- The boundary formula. For i + 1 ≥ dim Γ, with W the variables of
-- dimension i + 1 and S∓ the i-dimensional variables of ∂∓ᵢΓ,
--     ∂⁺W + S⁻ = ∂⁻W + S⁺.

private
  <-self : ∀ n → (n <ℕ n) ≡ false
  <-self zero    = refl
  <-self (suc n) = <-self n

  <-asym : ∀ a b → T (a <ℕ b) → (b <ℕ a) ≡ false
  <-asym zero    (suc b) _ = refl
  <-asym (suc a) (suc b) p = <-asym a b p

  <-not-≤ : ∀ a b → T (a <ℕ b) → (b <ℕ suc a) ≡ false
  <-not-≤ zero    (suc zero)    _ = refl
  <-not-≤ zero    (suc (suc b)) _ = refl
  <-not-≤ (suc a) (suc b)       p = <-not-≤ a b p

  ≡→==true : ∀ {a b} → a ≡ b → (a ==ℕ b) ≡ true
  ≡→==true {a} refl = ==-refl a

  -- Unfolding ∂∓ᵢ on one pasting extension.
  src-same : ∀ i Γ A B → (i <ℕ suc (dim A)) ≡ true → srcVars i (Γ ▸ A ▸ B) ≡ srcVars i Γ
  src-same i Γ A B p rewrite p = refl

  src-new : ∀ i Γ A B → (i <ℕ suc (dim A)) ≡ false →
            srcVars i (Γ ▸ A ▸ B) ≡ snoc (snoc (srcVars i Γ) (len Γ)) (suc (len Γ))
  src-new i Γ A B p rewrite p = refl

  tgt-swap : ∀ i Γ A B → (i <ℕ dim A) ≡ false → (dim A ==ℕ i) ≡ true →
             tgtVars i (Γ ▸ A ▸ B) ≡ snoc (dropLastᴸ (tgtVars i Γ)) (len Γ)
  tgt-swap i Γ A B p q rewrite p | q = refl

  tgt-new : ∀ i Γ A B → (i <ℕ dim A) ≡ false → (dim A ==ℕ i) ≡ false →
            tgtVars i (Γ ▸ A ▸ B) ≡ snoc (snoc (tgtVars i Γ) (len Γ)) (suc (len Γ))
  tgt-new i Γ A B p q rewrite p | q = refl

  dimv-y : ∀ Γ A B → dimv (Γ ▸ A ▸ B) (len Γ) ≡ dim A
  dimv-y Γ A B = cong dimM (trans (lookup-wk (Γ ▸ A) B (len Γ) (n<suc (len Γ))) (lookup-top Γ A))

  dimv-f : ∀ Γ A B → dimv (Γ ▸ A ▸ B) (suc (len Γ)) ≡ dim B
  dimv-f Γ A B = cong dimM (lookup-top (Γ ▸ A) B)

  swap-end : ∀ a b X → a ∷ (X ++ b ∷ []) ≈ b ∷ (X ++ a ∷ [])
  swap-end a b X =
    begin
      (a ∷ []) ++ (X ++ b ∷ [])
    ≈⟨ ++-comm (a ∷ []) (X ++ b ∷ []) ⟩
      (X ++ b ∷ []) ++ (a ∷ [])
    ≈⟨ ++-assoc X (b ∷ []) (a ∷ []) ⟩
      X ++ (b ∷ a ∷ [])
    ≈⟨ ++-cong (≈-refl {X}) (++-comm (b ∷ []) (a ∷ [])) ⟩
      X ++ (a ∷ b ∷ [])
    ≈⟨ ≈-sym (++-assoc X (a ∷ []) (b ∷ [])) ⟩
      (X ++ a ∷ []) ++ (b ∷ [])
    ≈⟨ ++-comm (X ++ a ∷ []) (b ∷ []) ⟩
      (b ∷ []) ++ (X ++ a ∷ [])
    ∎

Bnd : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i → T (dimCtx Γ <ℕ suc (suc i)) →
      cm (∂λ Γ true) (Wb Γ (suc i)) ++ sel Γ i (srcVars i Γ)
      ≈ cm (∂λ Γ false) (Wb Γ (suc i)) ++ sel Γ i (tgtVars i Γ)
Bnd pss i h = ≈-refl
Bnd (psd d) i h = Bnd d i h
Bnd (pse {Γ} {x} {A} d) i h = split (dim A ==ℕ i) refl
  where
  split : (b : Bool) → (dim A ==ℕ i) ≡ b →
          cm (∂λ (Γ ▸ A ▸ arr A (var x) (var (len Γ))) true) (Wb (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (suc i))
          ++ sel (Γ ▸ A ▸ arr A (var x) (var (len Γ))) i (srcVars i (Γ ▸ A ▸ arr A (var x) (var (len Γ))))
          ≈ cm (∂λ (Γ ▸ A ▸ arr A (var x) (var (len Γ))) false) (Wb (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (suc i))
          ++ sel (Γ ▸ A ▸ arr A (var x) (var (len Γ))) i (tgtVars i (Γ ▸ A ▸ arr A (var x) (var (len Γ))))
  split true e₂ = goal
    where
    n = len Γ
    B = arr A (var x) (var n)
    Γ′ = Γ ▸ A ▸ B
    hΓ : T (dimCtx Γ <ℕ suc (suc i))
    hΓ = max-≤ʳ (dim A) (dimCtx Γ) (suc (suc i)) (max-≤ʳ (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc (suc i)) h)
    eA : dim A ≡ i
    eA = ==→≡ (dim A) i e₂
    IH = Bnd d i hΓ
    P = cm (∂λ Γ true) (Wb Γ (suc i))
    N = cm (∂λ Γ false) (Wb Γ (suc i))
    S⁻ = sel Γ i (srcVars i Γ)
    D = sel Γ i (dropLastᴸ (tgtVars i Γ))

    cmW : ∀ b → cm (∂λ Γ′ b) (Wb Γ′ (suc i)) ≡ tup (if b then n else x) ∷ cm (∂λ Γ b) (Wb Γ (suc i))
    cmW b =
      trans (cong (cm (∂λ Γ′ b))
              (trans (sel-hit Γ′ (suc i) (suc n) (n ∷ downFrom n) (trans (dimv-f Γ A B) (cong suc eA)))
                     (cong (tup (suc n) ∷_)
                       (sel-miss Γ′ (suc i) n (downFrom n)
                         (trans (cong (_==ℕ suc i) (dimv-y Γ A B))
                                (<→≢ (dim A) (suc i) (subst (λ m → T (dim A <ℕ suc m)) eA (n<suc (dim A)))))))))
            (cong₂ _++_ (cong (∂T b) (lookup-top (Γ ▸ A) B))
                        (∂-ext₂ Γ A B b (suc i) (downFrom n) (Below-downFrom n)))

    src′ : sel Γ′ i (srcVars i Γ′) ≡ S⁻
    src′ = trans (cong (sel Γ′ i) (src-same i Γ A B (T→≡ (subst (λ m → T (i <ℕ suc m)) (sym eA) (n<suc i)))))
                 (sel-ext₂ Γ A B i (srcVars i Γ) (src-below i Γ))

    tgt′ : sel Γ′ i (tgtVars i Γ′) ≡ D ++ (tup n ∷ [])
    tgt′ = trans (cong (sel Γ′ i) (tgt-swap i Γ A B (subst (λ m → (i <ℕ m) ≡ false) (sym eA) (<-self i)) e₂))
          (trans (sel-++ Γ′ i (dropLastᴸ (tgtVars i Γ)) (n ∷ []))
                 (cong₂ _++_ (sel-ext₂ Γ A B i (dropLastᴸ (tgtVars i Γ)) (Below-dropLast n _ (tgt-below i Γ)))
                             (sel-hit Γ′ i n [] (trans (dimv-y Γ A B) eA))))

    -- ∂⁺ᵢΓ ends with x, the source of the new arrow.
    tΓ : sel Γ i (tgtVars i Γ) ≡ D ++ (tup x ∷ [])
    tΓ = trans (cong (sel Γ i) (lastL-split (tgtVars i Γ) x
                  (trans (tgt-last d i (subst (λ m → T (i <ℕ suc m)) (sym eA) (n<suc i)))
                         (cong just lastx))))
               (trans (sel-++ Γ i (dropLastᴸ (tgtVars i Γ)) (x ∷ []))
                      (cong (D ++_) (sel-hit Γ i x [] (trans (cong dimM (dang (ps-facts d))) eA))))
      where
      lastx : ti i x A ≡ x
      lastx rewrite e₂ = refl

    goal : cm (∂λ Γ′ true) (Wb Γ′ (suc i)) ++ sel Γ′ i (srcVars i Γ′)
           ≈ cm (∂λ Γ′ false) (Wb Γ′ (suc i)) ++ sel Γ′ i (tgtVars i Γ′)
    goal =
      begin
        cm (∂λ Γ′ true) (Wb Γ′ (suc i)) ++ sel Γ′ i (srcVars i Γ′)
      ≈⟨ ≡→≈ (cong₂ _++_ (cmW true) src′) ⟩
        tup n ∷ (P ++ S⁻)
      ≈⟨ ++-cong (≈-refl {tup n ∷ []}) (≈-trans IH (≡→≈ (cong (N ++_) tΓ))) ⟩
        tup n ∷ (N ++ (D ++ tup x ∷ []))
      ≈⟨ ≡→≈ (cong (tup n ∷_) (sym (++-assocL N D (tup x ∷ [])))) ⟩
        tup n ∷ ((N ++ D) ++ tup x ∷ [])
      ≈⟨ swap-end (tup n) (tup x) (N ++ D) ⟩
        tup x ∷ ((N ++ D) ++ tup n ∷ [])
      ≈⟨ ≡→≈ (cong (tup x ∷_) (++-assocL N D (tup n ∷ []))) ⟩
        tup x ∷ (N ++ (D ++ tup n ∷ []))
      ≈⟨ ≡→≈ (sym (cong₂ _++_ (cmW false) tgt′)) ⟩
        cm (∂λ Γ′ false) (Wb Γ′ (suc i)) ++ sel Γ′ i (tgtVars i Γ′)
      ∎
  split false e₂ = goal
    where
    n = len Γ
    B = arr A (var x) (var n)
    Γ′ = Γ ▸ A ▸ B
    hA : T (dim A <ℕ suc i)
    hA = max-≤ˡ (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc (suc i)) h
    hΓ : T (dimCtx Γ <ℕ suc (suc i))
    hΓ = max-≤ʳ (dim A) (dimCtx Γ) (suc (suc i)) (max-≤ʳ (suc (dim A)) (max (dim A) (dimCtx Γ)) (suc (suc i)) h)
    lt : T (dim A <ℕ i)
    lt = <suc-≢ (dim A) i hA e₂
    IH = Bnd d i hΓ
    E = sel Γ′ i (n ∷ []) ++ sel Γ′ i (suc n ∷ [])

    cmW : ∀ b → cm (∂λ Γ′ b) (Wb Γ′ (suc i)) ≡ cm (∂λ Γ b) (Wb Γ (suc i))
    cmW b =
      trans (cong (cm (∂λ Γ′ b))
              (trans (sel-miss Γ′ (suc i) (suc n) (n ∷ downFrom n) (trans (cong (_==ℕ suc i) (dimv-f Γ A B)) e₂))
                     (sel-miss Γ′ (suc i) n (downFrom n)
                       (trans (cong (_==ℕ suc i) (dimv-y Γ A B)) (<→≢ (dim A) (suc i) hA)))))
            (∂-ext₂ Γ A B b (suc i) (downFrom n) (Below-downFrom n))

    new : ∀ vs → Below n vs → sel Γ′ i (snoc (snoc vs n) (suc n)) ≡ sel Γ i vs ++ E
    new vs p =
      trans (sel-++ Γ′ i (snoc vs n) (suc n ∷ []))
     (trans (cong (_++ sel Γ′ i (suc n ∷ [])) (trans (sel-++ Γ′ i vs (n ∷ [])) (cong (_++ sel Γ′ i (n ∷ [])) (sel-ext₂ Γ A B i vs p))))
            (++-assocL (sel Γ i vs) _ _))

    goal : cm (∂λ Γ′ true) (Wb Γ′ (suc i)) ++ sel Γ′ i (srcVars i Γ′)
           ≈ cm (∂λ Γ′ false) (Wb Γ′ (suc i)) ++ sel Γ′ i (tgtVars i Γ′)
    goal =
      begin
        cm (∂λ Γ′ true) (Wb Γ′ (suc i)) ++ sel Γ′ i (srcVars i Γ′)
      ≈⟨ ≡→≈ (cong₂ _++_ (cmW true)
               (trans (cong (sel Γ′ i) (src-new i Γ A B (<-not-≤ (dim A) i lt))) (new (srcVars i Γ) (src-below i Γ)))) ⟩
        cm (∂λ Γ true) (Wb Γ (suc i)) ++ (sel Γ i (srcVars i Γ) ++ E)
      ≈⟨ ≈-sym (++-assoc (cm (∂λ Γ true) (Wb Γ (suc i))) (sel Γ i (srcVars i Γ)) E) ⟩
        (cm (∂λ Γ true) (Wb Γ (suc i)) ++ sel Γ i (srcVars i Γ)) ++ E
      ≈⟨ ++-cong IH (≈-refl {E}) ⟩
        (cm (∂λ Γ false) (Wb Γ (suc i)) ++ sel Γ i (tgtVars i Γ)) ++ E
      ≈⟨ ++-assoc (cm (∂λ Γ false) (Wb Γ (suc i))) (sel Γ i (tgtVars i Γ)) E ⟩
        cm (∂λ Γ false) (Wb Γ (suc i)) ++ (sel Γ i (tgtVars i Γ) ++ E)
      ≈⟨ ≡→≈ (sym (cong₂ _++_ (cmW false)
               (trans (cong (sel Γ′ i) (tgt-new i Γ A B (<-asym (dim A) i lt) e₂)) (new (tgtVars i Γ) (tgt-below i Γ))))) ⟩
        cm (∂λ Γ′ false) (Wb Γ′ (suc i)) ++ sel Γ′ i (tgtVars i Γ′)
      ∎

------------------------------------------------------------------------
-- ∂∓ᵢΓ has no repeated variables, so as a bag its i-dimensional part
-- counts each variable at most once.

NoDup : List Nat → Set
NoDup []       = ⊤
NoDup (x ∷ xs) = (elem x xs ≡ false) × NoDup xs

private
  ∨-false : ∀ a b → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false false false refl = refl , refl

  ==-sym-false : ∀ m n → (m ==ℕ n) ≡ false → (n ==ℕ m) ≡ false
  ==-sym-false zero    zero    ()
  ==-sym-false zero    (suc n) _ = refl
  ==-sym-false (suc m) zero    _ = refl
  ==-sym-false (suc m) (suc n) p = ==-sym-false m n p

elem-++ : ∀ v xs ys → elem v (xs ++ ys) ≡ (elem v xs ∨ elem v ys)
elem-++ v []       ys = refl
elem-++ v (x ∷ xs) ys with v ==ℕ x
... | true  = refl
... | false = elem-++ v xs ys

Below-elem : ∀ n xs → Below n xs → elem n xs ≡ false
Below-elem n []       _       = refl
Below-elem n (x ∷ xs) (p , q) rewrite <→≢′ x n p = Below-elem n xs q

NoDup-snoc : ∀ xs y → NoDup xs → elem y xs ≡ false → NoDup (snoc xs y)
NoDup-snoc []       y _       _ = refl , tt
NoDup-snoc (x ∷ xs) y (p , q) r =
  let (r₁ , r₂) = ∨-false (y ==ℕ x) (elem y xs) r in
  trans (elem-++ x xs (y ∷ [])) (helper (elem x xs) p (==-sym-false y x r₁)) ,
  NoDup-snoc xs y q r₂
  where
  helper : ∀ b → b ≡ false → (x ==ℕ y) ≡ false → (b ∨ ((x ==ℕ y) ∨ false)) ≡ false
  helper false refl e rewrite e = refl

elem-dropLast : ∀ v xs → elem v xs ≡ false → elem v (dropLastᴸ xs) ≡ false
elem-dropLast v []           _ = refl
elem-dropLast v (x ∷ [])     _ = refl
elem-dropLast v (x ∷ y ∷ xs) p =
  let (p₁ , p₂) = ∨-false (v ==ℕ x) _ p in
  helper p₁ (elem-dropLast v (y ∷ xs) p₂)
  where
  helper : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
  helper refl refl = refl

NoDup-dropLast : ∀ xs → NoDup xs → NoDup (dropLastᴸ xs)
NoDup-dropLast []           _       = tt
NoDup-dropLast (x ∷ [])     _       = tt
NoDup-dropLast (x ∷ y ∷ xs) (p , q) = elem-dropLast x (y ∷ xs) p , NoDup-dropLast (y ∷ xs) q

private
  NoDup-new : ∀ n xs → Below n xs → NoDup xs → NoDup (snoc (snoc xs n) (suc n))
  NoDup-new n xs b d =
    NoDup-snoc (snoc xs n) (suc n) (NoDup-snoc xs n d (Below-elem n xs b))
      (Below-elem (suc n) (snoc xs n)
        (Below-++ (suc n) xs (n ∷ []) (Below-suc n xs b) (n<suc n , tt)))

src-nodup : ∀ i Γ → NoDup (srcVars i Γ)
src-nodup i ε           = tt
src-nodup i (ε ▸ _)     = refl , tt
src-nodup i (Γ ▸ A ▸ B) with i <ℕ suc (dim A)
... | true  = src-nodup i Γ
... | false = NoDup-new (len Γ) _ (src-below i Γ) (src-nodup i Γ)

tgt-nodup : ∀ i Γ → NoDup (tgtVars i Γ)
tgt-nodup i ε           = tt
tgt-nodup i (ε ▸ _)     = refl , tt
tgt-nodup i (Γ ▸ A ▸ B) with i <ℕ dim A
... | true  = tgt-nodup i Γ
... | false with dim A ==ℕ i
...   | true  =
  NoDup-snoc (dropLastᴸ (tgtVars i Γ)) (len Γ)
    (NoDup-dropLast _ (tgt-nodup i Γ))
    (Below-elem (len Γ) _ (Below-dropLast (len Γ) _ (tgt-below i Γ)))
...   | false = NoDup-new (len Γ) _ (tgt-below i Γ) (tgt-nodup i Γ)

-- The count of (v) in the degree-k part of a list without repeats.
count-sel : ∀ Γ k v xs → NoDup xs →
            count (tup v) (sel Γ k xs) ≡ (if elem v xs then (if dimv Γ v ==ℕ k then 1 else 0) else 0)
count-sel Γ k v []       _       = refl
count-sel Γ k v (x ∷ xs) (p , q) with v ==ℕ x in e
... | true rewrite ==→≡ v x e = goal
  where
  zero-if-absent : count (tup x) (sel Γ k xs) ≡ 0
  zero-if-absent rewrite count-sel Γ k x xs q | p = refl
  goal : count (tup x) (sel Γ k (x ∷ xs)) ≡ (if dimv Γ x ==ℕ k then 1 else 0)
  goal with dimv Γ x ==ℕ k
  ... | true  rewrite ==-refl x = cong suc zero-if-absent
  ... | false = zero-if-absent
... | false = trans (skip (dimv Γ x ==ℕ k)) (count-sel Γ k v xs q)
  where
  skip : ∀ b → count (tup v) (if b then tup x ∷ sel Γ k xs else sel Γ k xs) ≡ count (tup v) (sel Γ k xs)
  skip true  rewrite e = refl
  skip false = refl

------------------------------------------------------------------------
-- ∂⁻ᵢΓ contains a variable of dimension i, for i ≤ dim Γ.

dim-≤-dimCtx : ∀ Γ v {A} → lookup Γ v ≡ just A → T (dim A <ℕ suc (dimCtx Γ))
dim-≤-dimCtx (Γ ▸ B) v {A} eq with v ==ℕ len Γ
... | true  rewrite sym (just-inj eq) = max-self (dim B) (dimCtx Γ)
  where
  max-self : ∀ a b → T (a <ℕ suc (max a b))
  max-self zero    b       = tt
  max-self (suc a) zero    = n<suc a
  max-self (suc a) (suc b) = max-self a b
... | false = lift (dimCtx Γ) (dim B) (dim-≤-dimCtx Γ v eq)
  where
  lift : ∀ c b → T (dim A <ℕ suc c) → T (dim A <ℕ suc (max b c))
  lift c b p = ≤-trans′ (dim A) c (max b c) p (max-≥ʳ b c)
    where
    max-≥ʳ : ∀ b c → T (c <ℕ suc (max b c))
    max-≥ʳ zero    c       = n<suc c
    max-≥ʳ (suc b) zero    = tt
    max-≥ʳ (suc b) (suc c) = max-≥ʳ b c
    ≤-trans′ : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ suc c) → T (a <ℕ suc c)
    ≤-trans′ zero    b       c       _ _ = tt
    ≤-trans′ (suc a) (suc b) (suc c) p q = ≤-trans′ a b c p q
    ≤-trans′ (suc a) zero    c       () _
    ≤-trans′ (suc a) (suc b) zero    _ ()

private
  ≤-<-trans : ∀ a c i → T (a <ℕ suc c) → T (c <ℕ i) → T (a <ℕ i)
  ≤-<-trans zero    c       (suc i) _ _ = tt
  ≤-<-trans (suc a) (suc c) (suc i) p q = ≤-<-trans a c i p q

  max-split : ∀ i a b → T (i <ℕ suc (max a b)) → T (b <ℕ i) → T (i <ℕ suc a)
  max-split zero    a       b       _ ()
  max-split (suc i) zero    b       p q = ⊥-elim (<-irrefl b (≤-<-trans b i b q p))
  max-split (suc i) (suc a) zero    p _ = p
  max-split (suc i) (suc a) (suc b) p q = max-split i a b p q

  squeeze : ∀ a i → T (a <ℕ i) → T (i <ℕ suc (suc a)) → i ≡ suc a
  squeeze zero    (suc zero)    _ _ = refl
  squeeze zero    (suc (suc i)) _ ()
  squeeze (suc a) (suc i)       p q = cong suc (squeeze a i p q)

  not-lt : ∀ i c → (i <ℕ suc c) ≡ false → T (c <ℕ i)
  not-lt zero    c       ()
  not-lt (suc i) zero    _ = tt
  not-lt (suc i) (suc c) p = not-lt i c p

  ∨-true : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-true false b p = p
  ∨-true true  b p = refl

  elem-snoc-snoc : ∀ v xs n m → elem v xs ≡ true → elem v (snoc (snoc xs n) m) ≡ true
  elem-snoc-snoc v xs n m p =
    trans (elem-++ v (snoc xs n) (m ∷ []))
      (subst (λ b → (b ∨ elem v (m ∷ [])) ≡ true)
        (sym (trans (elem-++ v xs (n ∷ [])) (cong (_∨ elem v (n ∷ [])) p))) refl)

elem-Below : ∀ n v xs → Below n xs → elem v xs ≡ true → T (v <ℕ n)
elem-Below n v (x ∷ xs) (p , q) e with v ==ℕ x in e′
... | true  rewrite ==→≡ v x e′ = p
... | false = elem-Below n v xs q e

src-has : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i → T (i <ℕ suc (dimCtx Γ)) →
          Σ Nat λ v → (elem v (srcVars i Γ) ≡ true) × (dimv Γ v ≡ i)
src-has pss zero    _ = 0 , refl , refl
src-has pss (suc i) ()
src-has (psd d) i p = src-has d i p
src-has (pse {Γ} {x} {A} d) i p = split (i <ℕ suc (dimCtx Γ)) refl
  where
  n = len Γ
  B = arr A (var x) (var n)
  Γ′ = Γ ▸ A ▸ B
  split : (b : Bool) → (i <ℕ suc (dimCtx Γ)) ≡ b →
          Σ Nat λ v → (elem v (srcVars i Γ′) ≡ true) × (dimv Γ′ v ≡ i)
  split true e =
    let (v , ev , dv) = src-has d i (≡→T e)
        lv = elem-Below n v (srcVars i Γ) (src-below i Γ) ev
    in v , stay (i <ℕ suc (dim A)) refl ev ,
       trans (dimv-wk (Γ ▸ A) B v (<-suc v n lv)) (trans (dimv-wk Γ A v lv) dv)
    where
    stay : (b : Bool) → (i <ℕ suc (dim A)) ≡ b → ∀ {v} → elem v (srcVars i Γ) ≡ true → elem v (srcVars i Γ′) ≡ true
    stay true  e′ {v} ev = trans (cong (elem v) (src-same i Γ A B e′)) ev
    stay false e′ {v} ev = trans (cong (elem v) (src-new i Γ A B e′)) (elem-snoc-snoc v (srcVars i Γ) n (suc n) ev)
  split false e = suc n , mem , trans (dimv-f Γ A B) (sym ieq)
    where
    cΓ : T (dimCtx Γ <ℕ i)
    cΓ = not-lt i (dimCtx Γ) e
    aΓ : T (dim A <ℕ suc (dimCtx Γ))
    aΓ = dim-≤-dimCtx Γ x (dang (ps-facts d))
    ai : T (dim A <ℕ i)
    ai = ≤-<-trans (dim A) (dimCtx Γ) i aΓ cΓ
    ieq : i ≡ suc (dim A)
    ieq = squeeze (dim A) i ai
            (max-split i (suc (dim A)) (max (dim A) (dimCtx Γ)) p (≤-max (dim A) (dimCtx Γ) i ai cΓ))
    mem : elem (suc n) (srcVars i Γ′) ≡ true
    mem = trans (cong (elem (suc n)) (src-new i Γ A B (<-not-≤ (dim A) i ai)))
            (trans (elem-++ (suc n) (snoc (srcVars i Γ) n) (suc n ∷ []))
                   (∨-true (elem (suc n) (snoc (srcVars i Γ) n)) _ (cong (_∨ false) (==-refl n))))

------------------------------------------------------------------------
-- Variables of ∂∓ᵢΓ have dimension at most i.

infixr 1 _⊎′_
data _⊎′_ (A B : Set) : Set where
  inl′ : A → A ⊎′ B
  inr′ : B → A ⊎′ B

private
  tgt-same : ∀ i Γ A B → (i <ℕ dim A) ≡ true → tgtVars i (Γ ▸ A ▸ B) ≡ tgtVars i Γ
  tgt-same i Γ A B p rewrite p = refl

  ∨-cases : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎′ (b ≡ true)
  ∨-cases true  b _ = inl′ refl
  ∨-cases false b p = inr′ p

  -- membership in xs ++ [n] ++ [m]
  elem-snoc : ∀ v xs y → elem v (snoc xs y) ≡ true → (elem v xs ≡ true) ⊎′ (v ≡ y)
  elem-snoc v xs y p with ∨-cases (elem v xs) _ (trans (sym (elem-++ v xs (y ∷ []))) p)
  ... | inl′ q = inl′ q
  ... | inr′ q with v ==ℕ y in e
  ...   | true  = inr′ (==→≡ v y e)
  ...   | false = ⊥-elim (f q)
    where
    f : false ≡ true → ⊥
    f ()

  elem-dropLast′ : ∀ v xs → elem v (dropLastᴸ xs) ≡ true → elem v xs ≡ true
  elem-dropLast′ v []           ()
  elem-dropLast′ v (x ∷ [])     ()
  elem-dropLast′ v (x ∷ y ∷ xs) p = ∨-mono (v ==ℕ x) (elem-dropLast′ v (y ∷ xs)) p
    where
    ∨-mono : ∀ {c d} b → (c ≡ true → d ≡ true) → (b ∨ c) ≡ true → (b ∨ d) ≡ true
    ∨-mono true  f _ = refl
    ∨-mono false f q = f q

  ≤-from-not-lt : ∀ a i → (i <ℕ suc a) ≡ false → T (suc a <ℕ suc i)
  ≤-from-not-lt a       zero    ()
  ≤-from-not-lt zero    (suc i) _ = tt
  ≤-from-not-lt (suc a) (suc i) p = ≤-from-not-lt a i p

  ≤-from-not-lt′ : ∀ a i → (i <ℕ a) ≡ false → T (a <ℕ suc i)
  ≤-from-not-lt′ zero    i       _ = tt
  ≤-from-not-lt′ (suc a) zero    ()
  ≤-from-not-lt′ (suc a) (suc i) p = ≤-from-not-lt′ a i p

  ≤-pred : ∀ a i → T (suc a <ℕ suc i) → T (a <ℕ suc i)
  ≤-pred a i p = <-suc a i p

dimv-wk₂ : ∀ Γ A B v → T (v <ℕ len Γ) → dimv (Γ ▸ A ▸ B) v ≡ dimv Γ v
dimv-wk₂ Γ A B v p = trans (dimv-wk (Γ ▸ A) B v (<-suc v (len Γ) p)) (dimv-wk Γ A v p)

src-dims : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i v → elem v (srcVars i Γ) ≡ true → T (dimv Γ v <ℕ suc i)
src-dims pss i v p with v ==ℕ 0 in e
... | true  = tt
... | false = ⊥-elim (f p)
  where
  f : false ≡ true → ⊥
  f ()
src-dims (psd d) i v p = src-dims d i v p
src-dims (pse {Γ} {x} {A} d) i v p = split (i <ℕ suc (dim A)) refl
  where
  n = len Γ
  B = arr A (var x) (var n)
  old : elem v (srcVars i Γ) ≡ true → T (dimv (Γ ▸ A ▸ B) v <ℕ suc i)
  old q rewrite dimv-wk₂ Γ A B v (elem-Below n v (srcVars i Γ) (src-below i Γ) q) = src-dims d i v q
  split : (b : Bool) → (i <ℕ suc (dim A)) ≡ b → T (dimv (Γ ▸ A ▸ B) v <ℕ suc i)
  split true  e = old (trans (cong (elem v) (sym (src-same i Γ A B e))) p)
  split false e with elem-snoc v (snoc (srcVars i Γ) n) (suc n)
                       (trans (cong (elem v) (sym (src-new i Γ A B e))) p)
  ... | inr′ refl rewrite dimv-f Γ A B = ≤-from-not-lt (dim A) i e
  ... | inl′ q with elem-snoc v (srcVars i Γ) n q
  ...   | inl′ r    = old r
  ...   | inr′ refl rewrite dimv-y Γ A B = ≤-pred (dim A) i (≤-from-not-lt (dim A) i e)

tgt-dims : ∀ {Γ z C} → Γ ⊢ps z ∶ C → ∀ i v → elem v (tgtVars i Γ) ≡ true → T (dimv Γ v <ℕ suc i)
tgt-dims pss i v p with v ==ℕ 0 in e
... | true  = tt
... | false = ⊥-elim (f p)
  where
  f : false ≡ true → ⊥
  f ()
tgt-dims (psd d) i v p = tgt-dims d i v p
tgt-dims (pse {Γ} {x} {A} d) i v p = split (i <ℕ dim A) refl
  where
  n = len Γ
  B = arr A (var x) (var n)
  old : elem v (tgtVars i Γ) ≡ true → T (dimv (Γ ▸ A ▸ B) v <ℕ suc i)
  old q rewrite dimv-wk₂ Γ A B v (elem-Below n v (tgtVars i Γ) (tgt-below i Γ) q) = tgt-dims d i v q
  split : (b : Bool) → (i <ℕ dim A) ≡ b → T (dimv (Γ ▸ A ▸ B) v <ℕ suc i)
  split true  e = old (trans (cong (elem v) (sym (tgt-same i Γ A B e))) p)
  split false e = split₂ (dim A ==ℕ i) refl
    where
    split₂ : (b : Bool) → (dim A ==ℕ i) ≡ b → T (dimv (Γ ▸ A ▸ B) v <ℕ suc i)
    split₂ true e₂ with elem-snoc v (dropLastᴸ (tgtVars i Γ)) n
                          (trans (cong (elem v) (sym (tgt-swap i Γ A B e e₂))) p)
    ... | inl′ q    = old (elem-dropLast′ v (tgtVars i Γ) q)
    ... | inr′ refl rewrite dimv-y Γ A B | ==→≡ (dim A) i e₂ = n<suc i
    split₂ false e₂ with elem-snoc v (snoc (tgtVars i Γ) n) (suc n)
                           (trans (cong (elem v) (sym (tgt-new i Γ A B e e₂))) p)
    ... | inr′ refl rewrite dimv-f Γ A B = <suc-≢ (dim A) i (≤-from-not-lt′ (dim A) i e) e₂
    ... | inl′ q with elem-snoc v (tgtVars i Γ) n q
    ...   | inl′ r    = old r
    ...   | inr′ refl rewrite dimv-y Γ A B = ≤-from-not-lt′ (dim A) i e

-- A pasting context of dimension 0 is a point.
ps-dim0 : ∀ {Γ z C} → Γ ⊢ps z ∶ C → dimCtx Γ ≡ 0 → Γ ≡ ε ▸ ⋆
ps-dim0 pss     _ = refl
ps-dim0 (psd d) p = ps-dim0 d p
ps-dim0 (pse {Γ} {x} {A} d) p = ⊥-elim (nz (dim A) (max (dim A) (dimCtx Γ)) p)
  where
  nz : ∀ a b → max (suc a) b ≡ 0 → ⊥
  nz a zero    ()
  nz a (suc b) ()
