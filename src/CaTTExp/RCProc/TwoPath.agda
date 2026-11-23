------------------------------------------------------------------------
-- 2-paths and exchange (ledger S20 (i), stage 3f of Theorem A,
-- notes/rc-generator.md §1, notes/relative-coherence.md §2 Step 4).
--
-- A 2-computad of dimension 2 is given abstractly (`Comp2`): 1-variables
-- with endpoints s₀, t₀, and 2-variables α with 1-path boundaries
-- ∂⁻ α ⇒ ∂⁺ α (lists of 1-variables, so composite boundaries are
-- allowed). A whiskered generator is (l, α, r) and acts on the 1-path
-- l ++ ∂⁻ α ++ r, giving l ++ ∂⁺ α ++ r. A 2-path is a list of whiskered
-- generators whose 1-boundaries chain (`Chain S P T`).
--
-- Exchange (`Xch`) swaps two adjacent generators acting on disjoint
-- segments:
--
--   (a, α, m ++ ∂⁻β ++ c) ; (a ++ ∂⁺α ++ m, β, c)
--     ⇄ (a ++ ∂⁻α ++ m, β, c) ; (a, α, m ++ ∂⁺β ++ c)
--
-- and _~_ is its equivalence closure. Both directions preserve chains
-- (`~-chain`), the bag of 2-variables (`~-bag`) and the length.
--
-- Theorem (3f, `exchange-complete`). Under a strong order up to
-- dimension 2 (`Key2`: key x < key e < key y for e : x → y, key e <
-- key α for e ∈ ∂⁻ α, key α < key e for e ∈ ∂⁺ α, and the boundaries
-- of each α are 1-paths a → b with key a < key b), two 2-paths with
-- the same source 1-path and the same bag of 2-variables are
-- exchange-equivalent.
--
-- Proof. Let μ be a 2-variable of least key in the bag. In any 2-path,
-- μ can be exchanged to the front (`front`): if β fires just before μ
-- and the target segment of β meets the source segment of μ in an edge
-- e, then key β < key e < key μ ≤ key β. So the two segments are
-- disjoint and the pair is an exchange. The source path of a 1-path
-- has strictly increasing keys, so ∂⁻ μ occurs in it at one place
-- only (`split-uniq`) and both 2-paths now start with the same
-- whiskered μ. Induct on the rest.
--
-- Also under Key2: a 1-path is determined by its start and its bag of
-- edges (`path-unique`).
--
-- Strong loop-freeness is needed: for g, h : f ⇒ f, the 2-paths g;h and
-- h;g have the same bag and source but are not exchange-equivalent
-- (Key2 fails, since key f < key g < key f). This counterexample is
-- on paper, not formalized.
------------------------------------------------------------------------
module CaTTExp.RCProc.TwoPath where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; <→≤; <-irrefl)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Lists and numbers.

infix 4 _∈_
data _∈_ (e : Nat) : List Nat → Set where
  here  : ∀ {xs} → e ∈ e ∷ xs
  there : ∀ {x xs} → e ∈ xs → e ∈ x ∷ xs

∈-++ʳ : ∀ {e} xs {ys} → e ∈ ys → e ∈ xs ++ ys
∈-++ʳ []       i = i
∈-++ʳ (x ∷ xs) i = there (∈-++ʳ xs i)

∈-tail : ∀ {β μ L} → (β ≡ μ → ⊥) → μ ∈ β ∷ L → μ ∈ L
∈-tail ne here      = ⊥-elim (ne refl)
∈-tail ne (there i) = i

-- Nonempty lists.
NE : List Nat → Set
NE p = Σ Nat λ d → Σ (List Nat) λ D → p ≡ d ∷ D

∷-inj : ∀ {x y : Nat} {xs ys} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
∷-inj refl = refl , refl

++-assoc≡ : ∀ (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc≡ []       ys zs = refl
++-assoc≡ (x ∷ xs) ys zs = cong (x ∷_) (++-assoc≡ xs ys zs)

-- (a ++ b ++ m) ++ d ≡ a ++ b ++ m ++ d
assoc4 : ∀ (a b m d : List Nat) → (a ++ b ++ m) ++ d ≡ a ++ b ++ m ++ d
assoc4 a b m d = trans (++-assoc≡ a (b ++ m) d) (cong (a ++_) (++-assoc≡ b m d))

++-cancelL : ∀ (l : List Nat) {a b} → l ++ a ≡ l ++ b → a ≡ b
++-cancelL []      e = e
++-cancelL (x ∷ l) e = ++-cancelL l (snd (∷-inj e))

dec≡ : ∀ (m n : Nat) → (m ≡ n) ⊎ (m ≡ n → ⊥)
dec≡ zero    zero    = inj₁ refl
dec≡ zero    (suc n) = inj₂ λ ()
dec≡ (suc m) zero    = inj₂ λ ()
dec≡ (suc m) (suc n) with dec≡ m n
... | inj₁ refl = inj₁ refl
... | inj₂ ne   = inj₂ λ { refl → ne refl }

==-refl≡ : ∀ n → (n ==ℕ n) ≡ true
==-refl≡ zero    = refl
==-refl≡ (suc n) = ==-refl≡ n

==-false : ∀ m n → (m ≡ n → ⊥) → (m ==ℕ n) ≡ false
==-false zero    zero    ne = ⊥-elim (ne refl)
==-false zero    (suc n) ne = refl
==-false (suc m) zero    ne = refl
==-false (suc m) (suc n) ne = ==-false m n λ e → ne (cong suc e)

≤-total : ∀ m n → (m ≤ n) ⊎ (n ≤ m)
≤-total zero    n       = inj₁ z≤n
≤-total (suc m) zero    = inj₂ z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans p q = ≤-trans p (<→≤ q)

<-≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
<-≤-trans p q = ≤-trans p q

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

------------------------------------------------------------------------
-- Splitting l ++ A ++ r = l' ++ B ++ r' with A, B nonempty: the two
-- segments are disjoint (one lies left of the other) or share an
-- element.

data Split (l A r l' B r' : List Nat) : Set where
  left  : ∀ m → l' ≡ l ++ A ++ m → r ≡ m ++ B ++ r' → Split l A r l' B r'
  right : ∀ m → l ≡ l' ++ B ++ m → r' ≡ m ++ A ++ r → Split l A r l' B r'
  meet  : ∀ e → e ∈ A → e ∈ B → Split l A r l' B r'

private
  pre : ∀ (A r l' B r' : List Nat) → NE B → A ++ r ≡ l' ++ B ++ r' →
        (Σ (List Nat) λ m → (l' ≡ A ++ m) × (r ≡ m ++ B ++ r')) ⊎ (Σ Nat λ e → (e ∈ A) × (e ∈ B))
  pre []      r l'       B r' _ eq = inj₁ (l' , refl , eq)
  pre (a ∷ A) r []       B r' (d , D , refl) eq with ∷-inj eq
  ... | refl , _ = inj₂ (a , here , here)
  pre (a ∷ A) r (x ∷ l') B r' nb eq with ∷-inj eq
  ... | refl , eq' with pre A r l' B r' nb eq'
  ...   | inj₁ (m , p , q) = inj₁ (m , cong (a ∷_) p , q)
  ...   | inj₂ (e , i , j) = inj₂ (e , there i , j)

split3 : ∀ (l A r l' B r' : List Nat) → NE A → NE B → l ++ A ++ r ≡ l' ++ B ++ r' → Split l A r l' B r'
split3 [] A r l' B r' na nb eq with pre A r l' B r' nb eq
... | inj₁ (m , p , q) = left m p q
... | inj₂ (e , i , j) = meet e i j
split3 (x ∷ l) A r [] B r' na nb eq with pre B r' (x ∷ l) A r na (sym eq)
... | inj₁ (m , p , q) = right m p q
... | inj₂ (e , i , j) = meet e j i
split3 (x ∷ l) A r (y ∷ l') B r' na nb eq with ∷-inj eq
... | refl , eq' with split3 l A r l' B r' na nb eq'
...   | left m p q  = left m (cong (x ∷_) p) q
...   | right m p q = right m (cong (x ∷_) p) q
...   | meet e i j  = meet e i j

------------------------------------------------------------------------
-- Bags of naturals.

cnt : Nat → List Nat → Nat
cnt a []      = 0
cnt a (x ∷ L) = if a ==ℕ x then suc (cnt a L) else cnt a L

infix 4 _≋_
record _≋_ (L M : List Nat) : Set where
  constructor mk≋
  field at≋ : ∀ a → cnt a L ≡ cnt a M
open _≋_ public

≋-sym : ∀ {L M} → L ≋ M → M ≋ L
≋-sym p = mk≋ λ a → sym (at≋ p a)

≋-trans : ∀ {L M N} → L ≋ M → M ≋ N → L ≋ N
≋-trans p q = mk≋ λ a → trans (at≋ p a) (at≋ q a)

≋-cons : ∀ x {L M} → L ≋ M → x ∷ L ≋ x ∷ M
≋-cons x p = mk≋ λ a → cong (λ n → if a ==ℕ x then suc n else n) (at≋ p a)

≋-swap : ∀ x y L → x ∷ y ∷ L ≋ y ∷ x ∷ L
≋-swap x y L = mk≋ λ a → sw (a ==ℕ x) (a ==ℕ y) (cnt a L)
  where
  sw : ∀ b c n → (if b then suc (if c then suc n else n) else (if c then suc n else n))
               ≡ (if c then suc (if b then suc n else n) else (if b then suc n else n))
  sw true  true  n = refl
  sw true  false n = refl
  sw false true  n = refl
  sw false false n = refl

≋-uncons : ∀ x {L M} → x ∷ L ≋ x ∷ M → L ≋ M
≋-uncons x p = mk≋ λ a → un (a ==ℕ x) (at≋ p a)
  where
  un : ∀ b {m n} → (if b then suc m else m) ≡ (if b then suc n else n) → m ≡ n
  un true  e = suc-inj e
  un false e = e

cnt-∈ : ∀ {a L} → a ∈ L → Σ Nat λ n → cnt a L ≡ suc n
cnt-∈ {a} {.a ∷ L} here rewrite ==-refl≡ a = cnt a L , refl
cnt-∈ {a} {x ∷ L} (there i) with a ==ℕ x
... | true  = cnt a L , refl
... | false = cnt-∈ i

∈-cnt : ∀ a L {n} → cnt a L ≡ suc n → a ∈ L
∈-cnt a []      ()
∈-cnt a (x ∷ L) e with a ==ℕ x in ax
... | true  rewrite ==ℕ-sound a x (subst T (sym ax) tt) = here
... | false = there (∈-cnt a L e)

≋-∈ : ∀ {L M a} → L ≋ M → a ∈ L → a ∈ M
≋-∈ {L} {M} {a} p i with cnt-∈ i
... | n , e = ∈-cnt a M (trans (sym (at≋ p a)) e)

------------------------------------------------------------------------
-- Abstract 2-computads.

record Comp2 : Set₁ where
  field
    E     : Nat → Set          -- 1-variables
    s₀ t₀ : Nat → Nat          -- their endpoints
    G     : Nat → Set          -- 2-variables
    ∂⁻ ∂⁺ : Nat → List Nat     -- their boundaries, as 1-paths
    key   : Nat → Nat

module TwoPaths (C : Comp2) where
  open Comp2 C

  ----------------------------------------------------------------------
  -- 1-paths.

  data Path1 : Nat → List Nat → Nat → Set where
    nil  : ∀ {x} → Path1 x [] x
    cons : ∀ {x e S y} → E e → s₀ e ≡ x → Path1 (t₀ e) S y → Path1 x (e ∷ S) y

  path-++ : ∀ {x m y l r} → Path1 x l m → Path1 m r y → Path1 x (l ++ r) y
  path-++ nil            q = q
  path-++ (cons ee s p)  q = cons ee s (path-++ p q)

  path-split : ∀ l {r x y} → Path1 x (l ++ r) y → Σ Nat λ m → Path1 x l m × Path1 m r y
  path-split []      p                = _ , nil , p
  path-split (e ∷ l) (cons ee s p) with path-split l p
  ... | m , p₁ , p₂ = m , cons ee s p₁ , p₂

  path-det : ∀ {x S y y'} → Path1 x S y → Path1 x S y' → y ≡ y'
  path-det nil           nil            = refl
  path-det (cons _ _ p)  (cons _ _ q)   = path-det p q

  ----------------------------------------------------------------------
  -- Whiskered generators, 2-paths and exchange.

  record WG : Set where
    constructor wg
    field
      l : List Nat
      g : Nat
      r : List Nat
  open WG public

  src1 tgt1 : WG → List Nat
  src1 (wg l g r) = l ++ ∂⁻ g ++ r
  tgt1 (wg l g r) = l ++ ∂⁺ g ++ r

  data Chain : List Nat → List WG → List Nat → Set where
    nil  : ∀ {S} → Chain S [] S
    cons : ∀ {S w P T} → G (g w) → src1 w ≡ S → Chain (tgt1 w) P T → Chain S (w ∷ P) T

  -- The 2-variables of a 2-path, in order.
  bagG : List WG → List Nat
  bagG []      = []
  bagG (w ∷ P) = g w ∷ bagG P

  lenW : List WG → Nat
  lenW []      = 0
  lenW (_ ∷ P) = suc (lenW P)

  data Xch : List WG → List WG → Set where
    xch  : ∀ a α m β c {P} →
           Xch (wg a α (m ++ ∂⁻ β ++ c) ∷ wg (a ++ ∂⁺ α ++ m) β c ∷ P)
               (wg (a ++ ∂⁻ α ++ m) β c ∷ wg a α (m ++ ∂⁺ β ++ c) ∷ P)
    skip : ∀ w {P Q} → Xch P Q → Xch (w ∷ P) (w ∷ Q)

  infix 4 _~_
  data _~_ : List WG → List WG → Set where
    done : ∀ {P} → P ~ P
    fwd  : ∀ {P Q R} → Xch P Q → Q ~ R → P ~ R
    bwd  : ∀ {P Q R} → Xch Q P → Q ~ R → P ~ R

  ~-trans : ∀ {P Q R} → P ~ Q → Q ~ R → P ~ R
  ~-trans done      q = q
  ~-trans (fwd x p) q = fwd x (~-trans p q)
  ~-trans (bwd x p) q = bwd x (~-trans p q)

  ~-sym : ∀ {P Q} → P ~ Q → Q ~ P
  ~-sym done      = done
  ~-sym (fwd x p) = ~-trans (~-sym p) (bwd x done)
  ~-sym (bwd x p) = ~-trans (~-sym p) (fwd x done)

  ~-cons : ∀ w {P Q} → P ~ Q → (w ∷ P) ~ (w ∷ Q)
  ~-cons w done      = done
  ~-cons w (fwd x p) = fwd (skip w x) (~-cons w p)
  ~-cons w (bwd x p) = bwd (skip w x) (~-cons w p)

  -- Exchange preserves chains, in both directions.
  xch-chain : ∀ {P Q S T} → Xch P Q → Chain S P T → Chain S Q T
  xch-chain (xch a α m β c) (cons Gα e₁ (cons Gβ e₂ ch)) =
    cons Gβ (trans (assoc4 a (∂⁻ α) m (∂⁻ β ++ c)) e₁)
      (cons Gα (sym (assoc4 a (∂⁻ α) m (∂⁺ β ++ c)))
        (subst (λ X → Chain X _ _) (assoc4 a (∂⁺ α) m (∂⁺ β ++ c)) ch))
  xch-chain (skip w x) (cons Gw e ch) = cons Gw e (xch-chain x ch)

  xch-chain⁻ : ∀ {P Q S T} → Xch P Q → Chain S Q T → Chain S P T
  xch-chain⁻ (xch a α m β c) (cons Gβ e₁ (cons Gα e₂ ch)) =
    cons Gα (trans (sym (assoc4 a (∂⁻ α) m (∂⁻ β ++ c))) e₁)
      (cons Gβ (assoc4 a (∂⁺ α) m (∂⁻ β ++ c))
        (subst (λ X → Chain X _ _) (sym (assoc4 a (∂⁺ α) m (∂⁺ β ++ c))) ch))
  xch-chain⁻ (skip w x) (cons Gw e ch) = cons Gw e (xch-chain⁻ x ch)

  ~-chain : ∀ {P Q S T} → P ~ Q → Chain S P T → Chain S Q T
  ~-chain done      c = c
  ~-chain (fwd x p) c = ~-chain p (xch-chain x c)
  ~-chain (bwd x p) c = ~-chain p (xch-chain⁻ x c)

  xch-bag : ∀ {P Q} → Xch P Q → bagG P ≋ bagG Q
  xch-bag (xch a α m β c {P}) = ≋-swap α β (bagG P)
  xch-bag (skip w x)          = ≋-cons (g w) (xch-bag x)

  ~-bag : ∀ {P Q} → P ~ Q → bagG P ≋ bagG Q
  ~-bag done      = mk≋ λ a → refl
  ~-bag (fwd x p) = ≋-trans (xch-bag x) (~-bag p)
  ~-bag (bwd x p) = ≋-trans (≋-sym (xch-bag x)) (~-bag p)

  xch-len : ∀ {P Q} → Xch P Q → lenW P ≡ lenW Q
  xch-len (xch _ _ _ _ _) = refl
  xch-len (skip w x)      = cong suc (xch-len x)

  ~-len : ∀ {P Q} → P ~ Q → lenW P ≡ lenW Q
  ~-len done      = refl
  ~-len (fwd x p) = trans (xch-len x) (~-len p)
  ~-len (bwd x p) = trans (sym (xch-len x)) (~-len p)

  ----------------------------------------------------------------------
  -- The strong order up to dimension 2.

  record Key2 : Set where
    field
      k₁ : ∀ e → E e → (key (s₀ e) < key e) × (key e < key (t₀ e))
      bd : ∀ α → G α → Σ Nat λ a → Σ Nat λ b →
           Path1 a (∂⁻ α) b × Path1 a (∂⁺ α) b × (key a < key b)
      k⁻ : ∀ α e → G α → e ∈ ∂⁻ α → key e < key α
      k⁺ : ∀ α e → G α → e ∈ ∂⁺ α → key α < key e

  module Theorem (K : Key2) where
    open Key2 K

    -- Keys strictly increase along a 1-path.
    path-gt : ∀ {x S y e} → Path1 x S y → e ∈ S → key x < key e
    path-gt {e = e} (cons {e = e₀} ee refl p) here = fst (k₁ e₀ ee)
    path-gt (cons {e = e₀} ee refl p) (there i) =
      <-trans (fst (k₁ e₀ ee)) (<-trans (snd (k₁ e₀ ee)) (path-gt p i))

    split-uniq : ∀ {x y} l₁ l₂ e r₁ r₂ → Path1 x (l₁ ++ e ∷ r₁) y → l₁ ++ e ∷ r₁ ≡ l₂ ++ e ∷ r₂ → l₁ ≡ l₂
    split-uniq []        []        e r₁ r₂ p eq = refl
    split-uniq []        (z ∷ l₂)  e r₁ r₂ (cons ee refl p) eq with ∷-inj eq
    ... | refl , eq' = ⊥-elim (<-irrefl (<-trans (snd (k₁ e ee))
                         (path-gt p (subst (e ∈_) (sym eq') (∈-++ʳ l₂ here)))))
    split-uniq (z ∷ l₁)  []        e r₁ r₂ (cons ee refl p) eq with ∷-inj eq
    ... | refl , eq' = ⊥-elim (<-irrefl (<-trans (snd (k₁ e ee)) (path-gt p (∈-++ʳ l₁ here))))
    split-uniq (z ∷ l₁)  (z' ∷ l₂) e r₁ r₂ (cons ee s p) eq with ∷-inj eq
    ... | refl , eq' = cong (z ∷_) (split-uniq l₁ l₂ e r₁ r₂ p eq')

    -- A 1-path is determined by its start and its bag of edges.
    path-unique : ∀ {x y y' p q} → Path1 x p y → Path1 x q y' → p ≋ q → p ≡ q
    path-unique nil nil b = refl
    path-unique {q = Q} nil (cons {e = f} _ _ _) b with cnt-∈ {f} {Q} here
    ... | k , e = ⊥-elim (z≢s (trans (at≋ b f) e))
      where
      z≢s : ∀ {k} → 0 ≡ suc k → ⊥
      z≢s ()
    path-unique {p = P} (cons {e = e} _ _ _) nil b with cnt-∈ {e} {P} here
    ... | k , c = ⊥-elim (z≢s (trans (sym (at≋ b e)) c))
      where
      z≢s : ∀ {k} → 0 ≡ suc k → ⊥
      z≢s ()
    path-unique (cons {e = e} ee refl p) (cons {e = f} ef sf q) b with dec≡ e f
    ... | inj₁ refl = cong (e ∷_) (path-unique p q (≋-uncons e b))
    ... | inj₂ ne = ⊥-elim (<-irrefl (<-trans kef kfe))
      where
      e∈q : e ∈ _
      e∈q = ∈-tail (λ z → ne (sym z)) (≋-∈ b here)
      f∈p : f ∈ _
      f∈p = ∈-tail ne (≋-∈ (≋-sym b) here)
      -- key f < key (t₀ f) < key e, and key e < key (t₀ e) < key f
      kfe : key f < key e
      kfe = <-trans (snd (k₁ f ef)) (path-gt q e∈q)
      kef : key e < key f
      kef = <-trans (snd (k₁ e ee)) (path-gt p f∈p)

    ne-path : ∀ {a p b} → Path1 a p b → key a < key b → NE p
    ne-path nil              lt = ⊥-elim (<-irrefl lt)
    ne-path (cons {e = e} {S = S} _ _ _) lt = e , S , refl

    ne⁻ : ∀ {α} → G α → NE (∂⁻ α)
    ne⁻ {α} Gα with bd α Gα
    ... | a , b , p , q , lt = ne-path p lt

    ne⁺ : ∀ {α} → G α → NE (∂⁺ α)
    ne⁺ {α} Gα with bd α Gα
    ... | a , b , p , q , lt = ne-path q lt

    -- Firing a generator keeps a 1-path a 1-path.
    fire : ∀ {x y} l α r → G α → Path1 x (l ++ ∂⁻ α ++ r) y → Path1 x (l ++ ∂⁺ α ++ r) y
    fire l α r Gα p with bd α Gα | path-split l p
    ... | a , b , pa , qa , lt | m , p₁ , p₂ with path-split (∂⁻ α) p₂
    ...   | n , p₃ , p₄ = path-++ p₁ (path-++ (subst (λ z → Path1 m (∂⁺ α) z) (sym bn) qm) p₄)
      where
      starts : ∀ {u v w z} {S} → NE S → Path1 u S v → Path1 w S z → u ≡ w
      starts (d , D , refl) (cons _ s₁ _) (cons _ s₂ _) = trans (sym s₁) s₂
      am : a ≡ m
      am = starts (ne-path pa lt) pa p₃
      qm : Path1 m (∂⁺ α) b
      qm = subst (λ z → Path1 z (∂⁺ α) b) am qa
      bn : n ≡ b
      bn = path-det p₃ (subst (λ z → Path1 z (∂⁻ α) b) am pa)

    -- The least key in a nonempty bag.
    least : ∀ x L → Σ Nat λ μ → (μ ∈ x ∷ L) × (∀ β → β ∈ x ∷ L → key μ ≤ key β)
    least x [] = x , here , λ { _ here → ≤-refl _ }
    least x (y ∷ L) with least y L
    ... | μ , i , h with ≤-total (key x) (key μ)
    ...   | inj₁ p = x , here , λ { _ here → ≤-refl _ ; β (there j) → ≤-trans p (h β j) }
    ...   | inj₂ p = μ , there i , λ { _ here → p ; β (there j) → h β j }

    -- Exchange a generator of least key to the front.
    front : ∀ {S T} (P : List WG) (μ : Nat) → Chain S P T → μ ∈ bagG P →
            (∀ β → β ∈ bagG P → key μ ≤ key β) →
            Σ (List Nat) λ l → Σ (List Nat) λ r → Σ (List WG) λ P' →
              (P ~ (wg l μ r ∷ P')) × Chain S (wg l μ r ∷ P') T
    front [] μ c () lst
    front (wg l β r ∷ P₀) μ (cons Gβ eS c₀) i lst with dec≡ β μ
    ... | inj₁ refl = l , r , P₀ , done , cons Gβ eS c₀
    ... | inj₂ β≢μ with front P₀ μ c₀ (∈-tail β≢μ i) (λ β' j → lst β' (there j))
    ...   | l' , r' , P₁ , e₀ , cons Gμ eS' c₁ with split3 l (∂⁺ β) r l' (∂⁻ μ) r' (ne⁺ Gβ) (ne⁻ Gμ) (sym eS')
    ...     | meet e e⁺ e⁻ =
                ⊥-elim (<-irrefl (<-≤-trans (<-trans (k⁺ β e Gβ e⁺) (k⁻ μ e Gμ e⁻)) (lst β here)))
    ...     | left m refl refl =
                (l ++ ∂⁻ β ++ m) , r' , (wg l β (m ++ ∂⁺ μ ++ r') ∷ P₁) ,
                ~-trans (~-cons _ e₀) (fwd (xch l β m μ r') done) ,
                xch-chain (xch l β m μ r') (cons Gβ eS (cons Gμ eS' c₁))
    ...     | right m refl refl =
                l' , (m ++ ∂⁻ β ++ r) , (wg (l' ++ ∂⁺ μ ++ m) β r ∷ P₁) ,
                ~-trans (~-cons _ e₀) (bwd (xch l' μ m β r) done) ,
                xch-chain⁻ (xch l' μ m β r) (cons Gβ eS (cons Gμ eS' c₁))

    -- Theorem (3f).
    complete : ∀ n {x y S T T'} (P Q : List WG) → lenW P ≡ n → Path1 x S y →
               Chain S P T → Chain S Q T' → bagG P ≋ bagG Q → P ~ Q
    complete _ [] [] _ _ _ _ _ = done
    complete _ [] (w ∷ Q) _ _ _ _ b with cnt-∈ {g w} {bagG (w ∷ Q)} here
    ... | k , e = ⊥-elim (z≢s (trans (at≋ b (g w)) e))
      where
      z≢s : ∀ {k} → 0 ≡ suc k → ⊥
      z≢s ()
    complete zero    (w ∷ P) Q () _ _ _ _
    complete (suc n) {x} {y} {S} (w ∷ P) Q len pS cP cQ b with least (g w) (bagG P)
    ... | μ , μ∈ , lstP
      with front (w ∷ P) μ cP μ∈ lstP
         | front Q μ cQ (≋-∈ b μ∈) (λ β j → lstP β (≋-∈ (≋-sym b) j))
    ... | l₁ , r₁ , P' , eP , cons Gμ e₁ cP' | l₂ , r₂ , Q' , eQ , cons _ e₂ cQ'
      with ne⁻ Gμ
    ... | d , D , dD with split-uniq l₁ l₂ d (D ++ r₁) (D ++ r₂)
                            (subst (λ X → Path1 x X y) (trans (sym e₁) (cong (λ Z → l₁ ++ Z ++ r₁) dD)) pS)
                            (trans (cong (λ Z → l₁ ++ Z ++ r₁) (sym dD))
                              (trans e₁ (trans (sym e₂) (cong (λ Z → l₂ ++ Z ++ r₂) dD))))
    ... | refl with ++-cancelL (∂⁻ μ) (++-cancelL l₁ (trans e₁ (sym e₂)))
    ... | refl =
      ~-trans eP (~-trans (~-cons (wg l₁ μ r₁) rec) (~-sym eQ))
      where
      pS' : Path1 x (l₁ ++ ∂⁺ μ ++ r₁) y
      pS' = fire l₁ μ r₁ Gμ (subst (λ X → Path1 x X y) (sym e₁) pS)
      lenP' : lenW P' ≡ n
      lenP' = suc-inj (trans (sym (~-len eP)) len)
      bag' : bagG P' ≋ bagG Q'
      bag' = ≋-uncons μ (≋-trans (≋-sym (~-bag eP)) (≋-trans b (~-bag eQ)))
      rec : P' ~ Q'
      rec = complete n P' Q' lenP' pS' cP' cQ' bag'

    exchange-complete : ∀ {x y S T T'} (P Q : List WG) → Path1 x S y →
                        Chain S P T → Chain S Q T' → bagG P ≋ bagG Q → P ~ Q
    exchange-complete P Q = complete (lenW P) P Q refl
