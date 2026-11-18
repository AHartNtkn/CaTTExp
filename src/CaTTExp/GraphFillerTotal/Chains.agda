------------------------------------------------------------------------
-- Chain contexts Θ_k = (x₀ —e₁→ x₁ —e₂→ … —e_k→ x_k), built directly
-- (not through pasting trees), with the arithmetic and lookup facts
-- needed by the totality proof of the 1-dimensional graph filler
-- (CaTTExp.GraphFillerTotal).
--
-- Levels: x₀ = 0, x_j = 2j − 1 and e_j = 2j for j ≥ 1, so
--   vtx j        = level of x_j,
--   edge (suc j) = level of e_{j+1}  (the edge from x_j to x_{j+1}).
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotal.Chains where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Weakening ∅ cattSide using (wk-ty)

------------------------------------------------------------------------
-- Order and arithmetic.

infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s p) = p

≤-+l : ∀ m n → n ≤ m + n
≤-+l zero    n = ≤-refl
≤-+l (suc m) n = ≤-step (≤-+l m n)

+-zero : ∀ n → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- m + n ≤ K implies n ≤ K and m ≤ K.
+≤→r : ∀ m n K → m + n ≤ K → n ≤ K
+≤→r m n K p = ≤-trans (≤-+l m n) p

+-mono-≤ : ∀ {m n} p → m ≤ n → p + m ≤ p + n
+-mono-≤ zero    q = q
+-mono-≤ (suc p) q = s≤s (+-mono-≤ p q)

≤-total : ∀ m n → m ≤ n ⊎ n < m
≤-total zero    n       = inj₁ z≤n
≤-total (suc m) zero    = inj₂ (s≤s z≤n)
≤-total (suc m) (suc n) with ≤-total m n
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

-- j ≤ suc k splits into j ≤ k or j ≡ suc k.
≤-suc-case : ∀ {j k} → j ≤ suc k → j ≤ k ⊎ j ≡ suc k
≤-suc-case {zero}  _ = inj₁ z≤n
≤-suc-case {suc j} {zero} (s≤s z≤n) = inj₂ refl
≤-suc-case {suc j} {suc k} (s≤s p) with ≤-suc-case p
... | inj₁ q = inj₁ (s≤s q)
... | inj₂ q = inj₂ (cong suc q)

-- Builtin comparisons.
<→T : ∀ {m n} → m < n → T (m <ℕ n)
<→T {zero}  (s≤s _) = tt
<→T {suc m} (s≤s p) = <→T p

T→< : ∀ m n → T (m <ℕ n) → m < n
T→< zero    (suc n) _ = s≤s z≤n
T→< (suc m) (suc n) p = s≤s (T→< m n p)

<→≢ : ∀ {m n} → m < n → (m ==ℕ n) ≡ false
<→≢ {zero}  {suc n} _       = refl
<→≢ {suc m} {suc n} (s≤s p) = <→≢ p

==-refl : ∀ n → (n ==ℕ n) ≡ true
==-refl zero    = refl
==-refl (suc n) = ==-refl n

------------------------------------------------------------------------
-- Positions in a chain.

dbl : Nat → Nat
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

vtx : Nat → Nat
vtx zero    = zero
vtx (suc j) = suc (dbl j)

edge : Nat → Nat
edge j = dbl j

dbl-mono : ∀ {m n} → m ≤ n → dbl m ≤ dbl n
dbl-mono z≤n     = z≤n
dbl-mono (s≤s p) = s≤s (s≤s (dbl-mono p))

vtx≤dbl : ∀ {j k} → j ≤ k → vtx j ≤ dbl k
vtx≤dbl {zero}             _       = z≤n
vtx≤dbl {suc j} {suc k}    (s≤s p) = s≤s (≤-step (dbl-mono p))

-- x_j comes before x_{k+1} when j ≤ k.
vtx-< : ∀ {j k} → j ≤ k → vtx j < vtx (suc k)
vtx-< p = s≤s (vtx≤dbl p)

vtx-mono : ∀ {j k} → j ≤ k → vtx j ≤ vtx k
vtx-mono {zero} _ = z≤n
vtx-mono {suc j} {suc k} (s≤s p) = s≤s (dbl-mono p)

-- e_{j+1} comes before x_{k+1} when j < k.
edge-< : ∀ {j k} → j < k → edge (suc j) < vtx (suc k)
edge-< {j} {suc k} (s≤s p) = s≤s (s≤s (s≤s (dbl-mono p)))

-- Every level is a vertex or an edge position.
data Parity : Nat → Set where
  isVtx  : ∀ j → Parity (vtx j)
  isEdge : ∀ j → Parity (edge (suc j))

parity : ∀ m → Parity m
parity zero = isVtx zero
parity (suc m) with parity m
... | isVtx zero    = isVtx (suc zero)
... | isVtx (suc j) = isEdge j
... | isEdge j      = isVtx (suc (suc j))

------------------------------------------------------------------------
-- Chain contexts.

chainC : Nat → Ctx
chainC zero    = ε ▸ ⋆
chainC (suc k) = chainC k ▸ ⋆ ▸ arr ⋆ (var (vtx k)) (var (vtx (suc k)))

len-chain : ∀ k → len (chainC k) ≡ vtx (suc k)
len-chain zero    = refl
len-chain (suc k) = cong (λ n → suc (suc n)) (len-chain k)

------------------------------------------------------------------------
-- Lookup.

lookup-here : ∀ Γ A i → i ≡ len Γ → lookup (Γ ▸ A) i ≡ just A
lookup-here Γ A _ refl rewrite ==-refl (len Γ) = refl

lookup-there : ∀ Γ A i → i < len Γ → lookup (Γ ▸ A) i ≡ lookup Γ i
lookup-there Γ A i p rewrite <→≢ p = refl

lookupₛ-here : ∀ σ t i → i ≡ lenₛ σ → lookupₛ (σ ,ₛ t) i ≡ t
lookupₛ-here σ t _ refl rewrite ==-refl (lenₛ σ) = refl

lookupₛ-there : ∀ σ t i → i < lenₛ σ → lookupₛ (σ ,ₛ t) i ≡ lookupₛ σ i
lookupₛ-there σ t i p rewrite <→≢ p = refl

<-len : ∀ {i} k → i < vtx (suc k) → i < len (chainC k)
<-len {i} k p = subst (i <_) (sym (len-chain k)) p

lookup-vtx : ∀ K j → j ≤ K → lookup (chainC K) (vtx j) ≡ just ⋆
lookup-vtx zero    zero    _ = refl
lookup-vtx (suc K) j p =
  trans (lookup-there (chainC K ▸ ⋆) _ (vtx j)
           (s≤s (subst (vtx j ≤_) (sym (len-chain K)) (vtx-mono p))))
        (go (≤-suc-case p))
  where
  go : j ≤ K ⊎ j ≡ suc K → lookup (chainC K ▸ ⋆) (vtx j) ≡ just ⋆
  go (inj₁ q)    = trans (lookup-there (chainC K) ⋆ (vtx j) (<-len K (vtx-< q)))
                         (lookup-vtx K j q)
  go (inj₂ refl) = lookup-here (chainC K) ⋆ (vtx (suc K)) (sym (len-chain K))

≤-case : ∀ {j k} → j ≤ k → j < k ⊎ j ≡ k
≤-case {zero} {zero} _ = inj₂ refl
≤-case {zero} {suc k} _ = inj₁ (s≤s z≤n)
≤-case {suc j} {suc k} (s≤s p) with ≤-case p
... | inj₁ q = inj₁ (s≤s q)
... | inj₂ q = inj₂ (cong suc q)

lookup-edge : ∀ K j → j < K →
              lookup (chainC K) (edge (suc j)) ≡ just (arr ⋆ (var (vtx j)) (var (vtx (suc j))))
lookup-edge (suc K) j (s≤s p) with ≤-case p
... | inj₂ refl = lookup-here (chainC K ▸ ⋆) _ (edge (suc K)) (cong suc (sym (len-chain K)))
... | inj₁ q =
  trans (lookup-there (chainC K ▸ ⋆) _ (edge (suc j)) (≤-step (<-len K (edge-< q))))
   (trans (lookup-there (chainC K) ⋆ (edge (suc j)) (<-len K (edge-< q)))
          (lookup-edge K j q))

------------------------------------------------------------------------
-- Chains are well formed pasting contexts.

chainC-wf : ∀ k → chainC k ⊢ctx
chainC-wf zero    = ▸-wf ε-wf (⋆-wf ε-wf)
chainC-wf (suc k) =
  ▸-wf w₁ (arr-wf
    (var-wf w₁ (trans (lookup-there (chainC k) ⋆ (vtx k) (<-len k (vtx-< ≤-refl)))
                      (lookup-vtx k k ≤-refl)))
    (var-wf w₁ (lookup-here (chainC k) ⋆ (vtx (suc k)) (sym (len-chain k)))))
  where
  w  = chainC-wf k
  w₁ = ▸-wf w (⋆-wf w)

chainC-ps : ∀ k → chainC k ⊢ps vtx k ∶ ⋆
chainC-ps zero    = pss
chainC-ps (suc k) =
  subst (λ n → chainC k ▸ ⋆ ▸ arr ⋆ (var (vtx k)) (var n) ⊢ps n ∶ ⋆)
        (len-chain k) (psd (pse (chainC-ps k)))

------------------------------------------------------------------------
-- Finite sets as lists.

infix 4 _∈_
_∈_ : Nat → List Nat → Set
m ∈ xs = T (elem m xs)

∨-inl : ∀ {a} b → T a → T (a ∨ b)
∨-inl {true} _ _ = tt

∨-inr : ∀ a {b} → T b → T (a ∨ b)
∨-inr true  _ = tt
∨-inr false p = p

∨-elim : ∀ a {b} → T (a ∨ b) → T a ⊎ T b
∨-elim true  _ = inj₁ tt
∨-elim false p = inj₂ p

∈-here : ∀ m xs → m ∈ m ∷ xs
∈-here m xs = ∨-inl (elem m xs) (subst T (sym (==-refl m)) tt)

∈-there : ∀ {m} x xs → m ∈ xs → m ∈ x ∷ xs
∈-there {m} x xs p = ∨-inr (m ==ℕ x) p

∈-++l : ∀ {m} xs ys → m ∈ xs → m ∈ xs ++ ys
∈-++l {m} (x ∷ xs) ys p with ∨-elim (m ==ℕ x) p
... | inj₁ q = ∨-inl (elem m (xs ++ ys)) q
... | inj₂ q = ∈-there x (xs ++ ys) (∈-++l xs ys q)

∈-++r : ∀ {m} xs ys → m ∈ ys → m ∈ xs ++ ys
∈-++r []       ys p = p
∈-++r (x ∷ xs) ys p = ∈-there x (xs ++ ys) (∈-++r xs ys p)

∈-++ : ∀ {m} xs ys → m ∈ xs ++ ys → m ∈ xs ⊎ m ∈ ys
∈-++ []       ys p = inj₂ p
∈-++ {m} (x ∷ xs) ys p with ∨-elim (m ==ℕ x) p
... | inj₁ q = inj₁ (∨-inl (elem m xs) q)
... | inj₂ q with ∈-++ xs ys q
...   | inj₁ r = inj₁ (∈-there x xs r)
...   | inj₂ r = inj₂ r

∈-single : ∀ {m j} → m ∈ j ∷ [] → m ≡ j
∈-single {m} {j} p with ∨-elim (m ==ℕ j) p
... | inj₁ q = ==ℕ-sound m j q

all-elim : ∀ (p : Nat → Bool) xs {m} → T (all p xs) → m ∈ xs → T (p m)
all-elim p (x ∷ xs) {m} h q with ∨-elim (m ==ℕ x) q
... | inj₁ r = subst (λ y → T (p y)) (sym (==ℕ-sound m x r)) (∧-fst h)
... | inj₂ r = all-elim p xs (∧-snd {p x} h) r

all-intro : ∀ (p : Nat → Bool) xs → (∀ m → m ∈ xs → T (p m)) → T (all p xs)
all-intro p []       f = tt
all-intro p (x ∷ xs) f = ∧-intro (f x (∈-here x xs)) (all-intro p xs (λ m q → f m (∈-there x xs q)))
  where
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

-- From a set equality with a singleton.
≈-single : ∀ {j} S → T (≈? (j ∷ []) S) → (j ∈ S) × (∀ m → m ∈ S → m ≡ j)
≈-single {j} S h =
  all-elim (λ x → elem x S) (j ∷ []) (∧-fst h) (∈-here j []) ,
  λ m q → ∈-single (all-elim (λ x → elem x (j ∷ [])) S (∧-snd {⊆? (j ∷ []) S} h) q)

elem-downFrom : ∀ {m n} → m < n → m ∈ downFrom n
elem-downFrom {m} {suc n} (s≤s p) with ≤-case p
... | inj₂ refl = ∈-here m (downFrom m)
... | inj₁ q    = ∈-there n (downFrom n) (elem-downFrom q)

------------------------------------------------------------------------
-- Recognising chains among pasting contexts.

private
  arr-inj₁ : ∀ {A B t u t' u'} → arr A t u ≡ arr B t' u' → A ≡ B
  arr-inj₁ refl = refl
  arr-inj₃ : ∀ {A B t u t' u'} → arr A t u ≡ arr B t' u' → u ≡ u'
  arr-inj₃ refl = refl
  var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
  var-inj refl = refl

  max-≤ : ∀ m n {k} → max m n ≤ k → m ≤ k × n ≤ k
  max-≤ zero    n       p = z≤n , p
  max-≤ (suc m) zero    p = p , z≤n
  max-≤ (suc m) (suc n) (s≤s p) = let (a , b) = max-≤ m n p in s≤s a , s≤s b

ChainShape : Ctx → Nat → Ty → Set
ChainShape Γ x A =
  Σ Nat λ k → (Γ ≡ chainC k) ×
    ((x ≡ vtx k × A ≡ ⋆) ⊎
     Σ Nat λ k' → (k ≡ suc k') × (x ≡ edge (suc k')) ×
                  (A ≡ arr ⋆ (var (vtx k')) (var (vtx (suc k')))))

-- A pasting context of dimension ≤ 1 is a chain.
ps-chain : ∀ {Γ x A} → Γ ⊢ps x ∶ A → dimCtx Γ ≤ 1 → ChainShape Γ x A
ps-chain pss _ = zero , refl , inj₁ (refl , refl)
ps-chain (pse {Γ} {x} {⋆} d) h with ps-chain d (snd (max-≤ 0 (dimCtx Γ) (snd (max-≤ 1 _ h))))
... | k , refl , inj₁ (refl , _) =
  suc k , cong (λ n → chainC k ▸ ⋆ ▸ arr ⋆ (var (vtx k)) (var n)) (len-chain k) ,
  inj₂ (k , refl , cong suc (len-chain k) ,
        cong (λ n → arr ⋆ (var (vtx k)) (var n)) (len-chain k))
... | k , refl , inj₂ (_ , _ , _ , ())
ps-chain (pse {Γ} {x} {arr B t u} d) h with fst (max-≤ (suc (dim (arr B t u))) (max (dim (arr B t u)) (dimCtx Γ)) h)
... | s≤s ()
ps-chain (psd d) h with ps-chain d h
... | k , refl , inj₁ (_ , ())
... | k , refl , inj₂ (k' , refl , _ , e) =
  suc k' , refl , inj₁ (var-inj (arr-inj₃ e) , arr-inj₁ e)

-- A pasting context that is not the point has 0 and 1 in every
-- positive-dimensional source.
SrcHas : Ctx → Set
SrcHas Γ = (Σ Ctx λ Γ₀ → Σ Ty λ B → Σ Ty λ C → Γ ≡ Γ₀ ▸ B ▸ C) ×
           (∀ i → (0 ∈ srcVars (suc i) Γ) × (1 ∈ srcVars (suc i) Γ))

private
  snoc-keep : ∀ {m} xs y → m ∈ xs → m ∈ snoc xs y
  snoc-keep xs y = ∈-++l xs (y ∷ [])

src-has : ∀ {Γ x A} → Γ ⊢ps x ∶ A → (Γ ≡ ε ▸ ⋆ × A ≡ ⋆) ⊎ SrcHas Γ
src-has pss = inj₁ (refl , refl)
src-has (pse {Γ} {x} {A} d) with src-has d
... | inj₁ (refl , refl) = inj₂ ((_ , _ , _ , refl) , λ i → tt , tt)
... | inj₂ (_ , has) = inj₂ ((_ , _ , _ , refl) , λ i → keep i)
  where
  keep : ∀ i → (0 ∈ srcVars (suc i) (Γ ▸ A ▸ arr A (var x) (var (len Γ)))) ×
               (1 ∈ srcVars (suc i) (Γ ▸ A ▸ arr A (var x) (var (len Γ))))
  keep i with suc i <ℕ suc (dim A)
  ... | true  = has i
  ... | false =
    let (a , b) = has i in
    let S = srcVars (suc i) Γ in
    snoc-keep (snoc S (len Γ)) (suc (len Γ)) (snoc-keep S (len Γ) a) ,
    snoc-keep (snoc S (len Γ)) (suc (len Γ)) (snoc-keep S (len Γ) b)
src-has (psd d) with src-has d
... | inj₁ (_ , ())
... | inj₂ h = inj₂ h

src-chain : ∀ k → srcVars 0 (chainC k) ≡ 0 ∷ []
src-chain zero    = refl
src-chain (suc k) = src-chain k

tgt-chain : ∀ k → tgtVars 0 (chainC k) ≡ vtx k ∷ []
tgt-chain zero    = refl
tgt-chain (suc k) rewrite tgt-chain k = cong (λ n → n ∷ []) (len-chain k)

-- The only 1-dimensional coherences are over chains, from the first
-- object to the last.
chain-side : ∀ {Θ j j'} → Θ ⊢ps → T (cattSide Θ ⋆ (var j) (var j')) →
             Σ Nat λ k → (Θ ≡ chainC k) × (j ≡ 0) × (j' ≡ vtx k)
chain-side {Θ} {j} {j'} (ps d) ok with ∨-elim (isCoh Θ ⋆ (var j) (var j')) ok
... | inj₁ c with src-has d
...   | inj₁ (refl , _) =
        let (_ , f) = ≈-single {j} (downFrom 1) (∧-fst c)
            (_ , g) = ≈-single {j'} (downFrom 1) (∧-snd {≈? (j ∷ []) (downFrom 1)} c) in
        zero , refl , sym (f 0 tt) , sym (g 0 tt)
...   | inj₂ ((Γ₀ , B , C , refl) , _) =
        let (_ , f) = ≈-single {j} (downFrom (len Θ)) (∧-fst c) in
        ⊥-elim (zero≢one (trans (f 0 (elem-downFrom {0} {len Θ} (s≤s z≤n)))
                                (sym (f 1 (elem-downFrom {1} {len Θ} (s≤s (s≤s z≤n)))))))
  where
  zero≢one : 0 ≡ 1 → ⊥
  zero≢one ()
chain-side {Θ} {j} {j'} (ps d) ok | inj₂ o with dimCtx Θ in eq
... | suc (suc i) with src-has d
...   | inj₁ (refl , _) with eq
...     | ()
chain-side {Θ} {j} {j'} (ps d) ok | inj₂ o | suc (suc i) | inj₂ (_ , has) =
  let (_ , f) = ≈-single {j} (srcVars (suc i) Θ) (∧-fst o)
      (a , b) = has i in
  ⊥-elim (zero≢one (trans (f 0 a) (sym (f 1 b))))
  where
  zero≢one : 0 ≡ 1 → ⊥
  zero≢one ()
chain-side {Θ} {j} {j'} (ps d) ok | inj₂ o | zero =
  small d (subst (_≤ 1) (sym eq) z≤n) (∧-fst o) (∧-snd {≈? (j ∷ []) (srcVars 0 Θ)} o)
  where
  small : ∀ {x} → Θ ⊢ps x ∶ ⋆ → dimCtx Θ ≤ 1 → T (≈? (j ∷ []) (srcVars 0 Θ)) →
          T (≈? (j' ∷ []) (tgtVars 0 Θ)) → Σ Nat λ k → (Θ ≡ chainC k) × (j ≡ 0) × (j' ≡ vtx k)
  small d le src tgt with ps-chain d le
  ... | k , refl , _ =
    k , refl , ∈-single (subst (j ∈_) (src-chain k) (fst (≈-single {j} (srcVars 0 (chainC k)) src))) ,
               ∈-single (subst (j' ∈_) (tgt-chain k) (fst (≈-single {j'} (tgtVars 0 (chainC k)) tgt)))
chain-side {Θ} {j} {j'} (ps d) ok | inj₂ o | suc zero =
  small d (subst (_≤ 1) (sym eq) ≤-refl) (∧-fst o) (∧-snd {≈? (j ∷ []) (srcVars 0 Θ)} o)
  where
  small : ∀ {x} → Θ ⊢ps x ∶ ⋆ → dimCtx Θ ≤ 1 → T (≈? (j ∷ []) (srcVars 0 Θ)) →
          T (≈? (j' ∷ []) (tgtVars 0 Θ)) → Σ Nat λ k → (Θ ≡ chainC k) × (j ≡ 0) × (j' ≡ vtx k)
  small d le src tgt with ps-chain d le
  ... | k , refl , _ =
    k , refl , ∈-single (subst (j ∈_) (src-chain k) (fst (≈-single {j} (srcVars 0 (chainC k)) src))) ,
               ∈-single (subst (j' ∈_) (tgt-chain k) (fst (≈-single {j'} (tgtVars 0 (chainC k)) tgt)))
