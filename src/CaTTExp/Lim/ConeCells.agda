------------------------------------------------------------------------
-- The specified cone on cells, in every dimension, and the boundary
-- part of its well-typedness (notes/specified-cones.md, Lemma 2.2).
--
-- A cell is a CaTT term with its type (CaTTExp.Cones.Cell). The binary
-- composite u ∗_k w of two cells is the coherence term of
-- CaTTExp.Cones.binC, typed by recursion on the boundaries:
--
--   u ∗_k w : ∂⁻u ∗_k ∂⁻w → ∂⁺u ∗_k ∂⁺w     (a factor of lower dimension
--                                            than the composite is kept)
--   u ∗_k w : ∂⁻u → ∂⁺w                      (both factors of dimension k+1)
--
-- (`bcell`). This is the typing Mikhail's composites carry; CaTTExp.Cones
-- computes the same recursion on expressions (`tyF`).
--
-- The specified cone (Mikhail, Thm 3.3; spec §6.1) over a cell t of
-- dimension m, with apex c and projections p:
--
--   p_x : c → x                                     (m = 0)
--   p_t : p_{τt} → T_t,   T_t = p_{σt} ∗_{m−1} (p_{σ²t} ∗_{m−2} (… (p_{σᵐt} ∗₀ t)))
--
-- `projN` gives the type of p_t from t's cell alone: the iterated
-- sources and targets of t are read off its type, so no context is
-- consulted. Lemma 2.2 is proved here for every cell:
--
--   * `chain-src`, `chain-tgt`: taking a boundary of a partial long side
--     V = p_{σʲt} ∗ (… (p_{σᵐt} ∗₀ t)) (j ≥ 2) commutes with the chain:
--     ∂^α V_t = V_{∂^α t};
--   * `T-par`: T_t has the type of p_{τt}, so the type of p_t is well
--     formed (its two sides are parallel);
--   * `chain-comp`: every composite in T_t is composable: the k-target
--     of its left factor is the k-source of its right factor.
--
-- These are the boundary claims. That each binary composite is a
-- well-typed CaTT term over its glued pasting tree (typing of binC) is
-- not proved here (ledger B22).
------------------------------------------------------------------------
module CaTTExp.Lim.ConeCells where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones using (Cell; dimC; srcC; tgtC; binC)

------------------------------------------------------------------------
-- Arithmetic.

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

private
  lt-irr : ∀ m → (m <ℕ m) ≡ false
  lt-irr zero    = refl
  lt-irr (suc m) = lt-irr m

  eq-refl : ∀ m → (m ==ℕ m) ≡ true
  eq-refl zero    = refl
  eq-refl (suc m) = eq-refl m

  lt-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
  lt-trans zero    (suc b) (suc c) _ _ = tt
  lt-trans (suc a) (suc b) (suc c) p q = lt-trans a b c p q

  lt-suc : ∀ a → T (a <ℕ suc a)
  lt-suc zero    = tt
  lt-suc (suc a) = lt-suc a

  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

  -- x < max x y forces max x y = y.
  max-lt-l : ∀ x y → T (x <ℕ max x y) → max x y ≡ y
  max-lt-l zero    zero    ()
  max-lt-l zero    (suc y) _ = refl
  max-lt-l (suc x) zero    p = ⊥-elim (subst T (lt-irr x) p)
  max-lt-l (suc x) (suc y) p = cong suc (max-lt-l x y p)

  max-lt-r : ∀ x y → T (y <ℕ max x y) → max x y ≡ x
  max-lt-r zero    zero    ()
  max-lt-r zero    (suc y) p = ⊥-elim (subst T (lt-irr y) p)
  max-lt-r (suc x) zero    _ = refl
  max-lt-r (suc x) (suc y) p = cong suc (max-lt-r x y p)

  -- not (x < max x y) forces max x y = x.
  max-nlt-l : ∀ x y → (x <ℕ max x y) ≡ false → max x y ≡ x
  max-nlt-l zero    zero    _ = refl
  max-nlt-l zero    (suc y) ()
  max-nlt-l (suc x) zero    _ = refl
  max-nlt-l (suc x) (suc y) p = cong suc (max-nlt-l x y p)

  max-nlt-r : ∀ x y → (y <ℕ max x y) ≡ false → max x y ≡ y
  max-nlt-r zero    zero    _ = refl
  max-nlt-r zero    (suc y) _ = refl
  max-nlt-r (suc x) zero    ()
  max-nlt-r (suc x) (suc y) p = cong suc (max-nlt-r x y p)

  max-idem : ∀ x → max x x ≡ x
  max-idem zero    = refl
  max-idem (suc x) = cong suc (max-idem x)

  -- a < b gives max a (pred b) = pred b.
  max-pred : ∀ a b → T (a <ℕ b) → max a (pred b) ≡ pred b
  max-pred zero    (suc b) _ = refl
  max-pred (suc a) (suc (suc b)) p = cong suc (max-pred a (suc b) p)
  max-pred (suc a) (suc zero) p = ⊥-elim (lt0 a p)
    where
    lt0 : ∀ a → T (a <ℕ 0) → ⊥
    lt0 _ ()

  max-comm : ∀ x y → max x y ≡ max y x
  max-comm zero    zero    = refl
  max-comm zero    (suc y) = refl
  max-comm (suc x) zero    = refl
  max-comm (suc x) (suc y) = cong suc (max-comm x y)

  -- The dimension of a lowered factor.
  gl : Nat → Nat → Nat
  gl r z = if z <ℕ r then z else pred z

  max-gl : ∀ x y → max (gl (max x y) x) (gl (max x y) y) ≡ pred (max x y)
  max-gl x y with x <ℕ max x y in ex | y <ℕ max x y in ey
  ... | true  | true  =
    ⊥-elim (subst T (trans (cong (y <ℕ_) (max-lt-l x y (subst T (sym ex) tt))) (lt-irr y))
                    (subst T (sym ey) tt))
  ... | true  | false =
    trans (max-pred x y (subst (λ r → T (x <ℕ r)) e (subst T (sym ex) tt))) (cong pred (sym e))
    where e = max-lt-l x y (subst T (sym ex) tt)
  ... | false | true  =
    trans (max-comm (pred x) y)
          (trans (max-pred y x (subst (λ r → T (y <ℕ r)) e (subst T (sym ey) tt))) (cong pred (sym e)))
    where e = max-lt-r x y (subst T (sym ey) tt)
  ... | false | false =
    trans (cong₂ (λ a b → max (pred a) (pred b)) (sym (max-nlt-l x y ex)) (sym (max-nlt-r x y ey)))
          (max-idem (pred (max x y)))

------------------------------------------------------------------------
-- Boundaries of cells.

dim-src : ∀ c → dimC (srcC c) ≡ pred (dimC c)
dim-src (t , ⋆)       = refl
dim-src (t , arr A s u) = refl

dim-tgt : ∀ c → dimC (tgtC c) ≡ pred (dimC c)
dim-tgt (t , ⋆)       = refl
dim-tgt (t , arr A s u) = refl

-- A boundary depends only on the type, once the dimension is positive.
src-type : ∀ {a b} → snd a ≡ snd b → T (0 <ℕ dimC a) → srcC a ≡ srcC b
src-type {ta , arr A s u} {tb , .(arr A s u)} refl _ = refl

tgt-type : ∀ {a b} → snd a ≡ snd b → T (0 <ℕ dimC a) → tgtC a ≡ tgtC b
tgt-type {ta , arr A s u} {tb , .(arr A s u)} refl _ = refl

-- The two boundaries of a cell have the same type.
src-tgt-type : ∀ c → snd (srcC c) ≡ snd (tgtC c)
src-tgt-type (t , ⋆)         = refl
src-tgt-type (t , arr A s u) = refl

------------------------------------------------------------------------
-- Typed binary composites.

loC hiC : Nat → Cell → Cell
loC r c = if dimC c <ℕ r then c else srcC c
hiC r c = if dimC c <ℕ r then c else tgtC c

mutual
  bcellR : Nat → Nat → Cell → Cell → Cell
  bcellR r k u w = fst (binC k u w) , btyR r k u w

  btyR : Nat → Nat → Cell → Cell → Ty
  btyR zero     k u w = ⋆
  btyR (suc r′) k u w =
    if r′ ==ℕ k then arr (snd (srcC u)) (fst (srcC u)) (fst (tgtC w))
    else arr (snd (bcellR r′ k (loC (suc r′) u) (loC (suc r′) w)))
             (fst (bcellR r′ k (loC (suc r′) u) (loC (suc r′) w)))
             (fst (bcellR r′ k (hiC (suc r′) u) (hiC (suc r′) w)))

-- u ∗_k w, with r the larger dimension.
bcell : Nat → Cell → Cell → Cell
bcell k u w = bcellR (max (dimC u) (dimC w)) k u w

dim-lo : ∀ r c → dimC (loC r c) ≡ gl r (dimC c)
dim-lo r c with dimC c <ℕ r
... | true  = refl
... | false = dim-src c

dim-hi : ∀ r c → dimC (hiC r c) ≡ gl r (dimC c)
dim-hi r c with dimC c <ℕ r
... | true  = refl
... | false = dim-tgt c

lo-max : ∀ u w → let r = max (dimC u) (dimC w) in
         max (dimC (loC r u)) (dimC (loC r w)) ≡ pred r
lo-max u w = trans (cong₂ max (dim-lo (max (dimC u) (dimC w)) u) (dim-lo (max (dimC u) (dimC w)) w)) (max-gl (dimC u) (dimC w))

hi-max : ∀ u w → let r = max (dimC u) (dimC w) in
         max (dimC (hiC r u)) (dimC (hiC r w)) ≡ pred r
hi-max u w = trans (cong₂ max (dim-hi (max (dimC u) (dimC w)) u) (dim-hi (max (dimC u) (dimC w)) w)) (max-gl (dimC u) (dimC w))

private
  -- max a b = suc k with k < a forces a = suc k.
  max-top-l : ∀ a b k → T (k <ℕ a) → max a b ≡ suc k → a ≡ suc k
  max-top-l (suc a) zero    k _ e = e
  max-top-l (suc a) (suc b) zero    _ e = cong suc (lem a b (suc-inj e))
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
    lem : ∀ a b → max a b ≡ 0 → a ≡ 0
    lem zero    _       _ = refl
    lem (suc a) zero    ()
    lem (suc a) (suc b) ()
  max-top-l (suc a) (suc b) (suc k) p e = cong suc (max-top-l a b k p (suc-inj e))
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

  -- k < suc r′ and r′ ≠ k give k < r′.
  lt-ne : ∀ k r′ → T (k <ℕ suc r′) → (r′ ==ℕ k) ≡ false → T (k <ℕ r′)
  lt-ne zero    zero    _ ()
  lt-ne zero    (suc r′) _ _ = tt
  lt-ne (suc k) zero    p _ = ⊥-elim (lt0 k p)
    where
    lt0 : ∀ a → T (a <ℕ 0) → ⊥
    lt0 _ ()
  lt-ne (suc k) (suc r′) p e = lt-ne k r′ p e

  -- a factor of a composite along k, of dimension above k, stays above
  -- k when lowered.
  lt-gl : ∀ k r′ a → T (k <ℕ a) → T (k <ℕ r′) → (a <ℕ suc r′) ≡ false → T (k <ℕ pred a)
  lt-gl k r′ (suc a) p q e = lt-trans′ k r′ a q (nlt a r′ e)
    where
    nlt : ∀ a r′ → (a <ℕ r′) ≡ false → T (r′ <ℕ suc a)
    nlt a       zero    _ = tt
    nlt zero    (suc r′) ()
    nlt (suc a) (suc r′) e = nlt a r′ e
    lt-trans′ : ∀ k r′ a → T (k <ℕ r′) → T (r′ <ℕ suc a) → T (k <ℕ a)
    lt-trans′ zero    (suc r′) (suc a) _ _ = tt
    lt-trans′ zero    (suc r′) zero    _ q = ⊥-elim (lt0 r′ q)
      where
      lt0 : ∀ a → T (a <ℕ 0) → ⊥
      lt0 _ ()
    lt-trans′ (suc k) (suc r′) (suc a) p q = lt-trans′ k r′ a p q
    lt-trans′ (suc k) (suc r′) zero    p q = ⊥-elim (lt0 r′ q)
      where
      lt0 : ∀ a → T (a <ℕ 0) → ⊥
      lt0 _ ()

  le-max-l : ∀ a b → (max a b <ℕ a) ≡ false
  le-max-l zero    b       = refl
  le-max-l (suc a) zero    = lt-irr a
  le-max-l (suc a) (suc b) = le-max-l a b

-- A factor of dimension above k keeps it after lowering.
lo-above : ∀ k r′ c → T (k <ℕ dimC c) → T (k <ℕ r′) → T (k <ℕ dimC (loC (suc r′) c))
lo-above k r′ c p q with dimC c <ℕ suc r′ in e
... | true  = p
... | false = subst (λ n → T (k <ℕ n)) (sym (dim-src c)) (lt-gl k r′ (dimC c) p q e)

hi-above : ∀ k r′ c → T (k <ℕ dimC c) → T (k <ℕ r′) → T (k <ℕ dimC (hiC (suc r′) c))
hi-above k r′ c p q with dimC c <ℕ suc r′ in e
... | true  = p
... | false = subst (λ n → T (k <ℕ n)) (sym (dim-tgt c)) (lt-gl k r′ (dimC c) p q e)

-- The dimension of a composite is the larger dimension of its factors.
bcellR-dim : ∀ r k u w → max (dimC u) (dimC w) ≡ r → T (k <ℕ dimC u) → T (k <ℕ dimC w) →
             dimC (bcellR r k u w) ≡ r
bcellR-dim zero k u w e p q = ⊥-elim (subst (λ n → T (k <ℕ n)) (max-zero (dimC u) (dimC w) e) p)
  where
  max-zero : ∀ a b → max a b ≡ 0 → a ≡ 0
  max-zero zero    _       _ = refl
  max-zero (suc a) zero    ()
  max-zero (suc a) (suc b) ()
  _ : ⊤
  _ = tt
bcellR-dim (suc r′) k u w e p q with r′ ==ℕ k in ek
... | true rewrite ==ℕ-sound r′ k (subst T (sym ek) tt) =
  trans (cong suc (dim-src u)) (cong (λ n → suc (pred n)) (max-top-l (dimC u) (dimC w) k p e))
... | false =
  cong suc (bcellR-dim r′ k (loC (suc r′) u) (loC (suc r′) w)
              (subst (λ M → max (dimC (loC M u)) (dimC (loC M w)) ≡ pred M) e (lo-max u w))
              (lo-above k r′ u p kr) (lo-above k r′ w q kr))
  where
  kr : T (k <ℕ r′)
  kr = lt-ne k r′ (subst (λ n → T (k <ℕ n)) e (lt-max k (dimC u) (dimC w) p)) ek
    where
    lt-max : ∀ k a b → T (k <ℕ a) → T (k <ℕ max a b)
    lt-max zero    (suc a) zero    _ = tt
    lt-max zero    (suc a) (suc b) _ = tt
    lt-max (suc k) (suc a) zero    p = p
    lt-max (suc k) (suc a) (suc b) p = lt-max k a b p

------------------------------------------------------------------------
-- Boundaries of a composite.

bcell-at : ∀ {r} k u w → max (dimC u) (dimC w) ≡ r → bcell k u w ≡ bcellR r k u w
bcell-at k u w e = cong (λ r → bcellR r k u w) e

-- Both factors of dimension k+1: u ∗_k w : ∂⁻u → ∂⁺w.
bcR-src-c : ∀ k u w → srcC (bcellR (suc k) k u w) ≡ srcC u
bcR-src-c k u w rewrite eq-refl k = refl

bcR-tgt-c : ∀ k u w → tgtC (bcellR (suc k) k u w) ≡ (fst (tgtC w) , snd (srcC u))
bcR-tgt-c k u w rewrite eq-refl k = refl

bcR-ty-c : ∀ k u w → snd (bcellR (suc k) k u w) ≡ arr (snd (srcC u)) (fst (srcC u)) (fst (tgtC w))
bcR-ty-c k u w rewrite eq-refl k = refl

-- Otherwise the boundaries are composites of the boundaries.
bcR-src-nc : ∀ r′ k u w → (r′ ==ℕ k) ≡ false →
  srcC (bcellR (suc r′) k u w) ≡ bcellR r′ k (loC (suc r′) u) (loC (suc r′) w)
bcR-src-nc r′ k u w e rewrite e = refl

bcR-tgt-nc : ∀ r′ k u w → (r′ ==ℕ k) ≡ false →
  tgtC (bcellR (suc r′) k u w)
  ≡ (fst (bcellR r′ k (hiC (suc r′) u) (hiC (suc r′) w)) , snd (bcellR r′ k (loC (suc r′) u) (loC (suc r′) w)))
bcR-tgt-nc r′ k u w e rewrite e = refl

-- In terms of bcell.
bc-src-nc : ∀ r′ k u w → max (dimC u) (dimC w) ≡ suc r′ → (r′ ==ℕ k) ≡ false →
  srcC (bcell k u w) ≡ bcell k (loC (suc r′) u) (loC (suc r′) w)
bc-src-nc r′ k u w e ek =
  trans (cong srcC (bcell-at k u w e))
    (trans (bcR-src-nc r′ k u w ek)
      (sym (bcell-at k _ _ (subst (λ M → max (dimC (loC M u)) (dimC (loC M w)) ≡ pred M) e (lo-max u w)))))

bc-tgt-nc : ∀ r′ k u w → max (dimC u) (dimC w) ≡ suc r′ → (r′ ==ℕ k) ≡ false →
  tgtC (bcell k u w) ≡ (fst (bcell k (hiC (suc r′) u) (hiC (suc r′) w)) , snd (bcell k (loC (suc r′) u) (loC (suc r′) w)))
bc-tgt-nc r′ k u w e ek =
  trans (cong tgtC (bcell-at k u w e))
    (trans (bcR-tgt-nc r′ k u w ek)
      (cong₂ _,_
        (cong fst (sym (bcell-at k _ _ (subst (λ M → max (dimC (hiC M u)) (dimC (hiC M w)) ≡ pred M) e (hi-max u w)))))
        (cong snd (sym (bcell-at k _ _ (subst (λ M → max (dimC (loC M u)) (dimC (loC M w)) ≡ pred M) e (lo-max u w)))))))

bc-src-c : ∀ k u w → max (dimC u) (dimC w) ≡ suc k → srcC (bcell k u w) ≡ srcC u
bc-src-c k u w e = trans (cong srcC (bcell-at k u w e)) (bcR-src-c k u w)

bc-tgt-c : ∀ k u w → max (dimC u) (dimC w) ≡ suc k → tgtC (bcell k u w) ≡ (fst (tgtC w) , snd (srcC u))
bc-tgt-c k u w e = trans (cong tgtC (bcell-at k u w e)) (bcR-tgt-c k u w)

bc-ty-c : ∀ k u w → max (dimC u) (dimC w) ≡ suc k →
  snd (bcell k u w) ≡ arr (snd (srcC u)) (fst (srcC u)) (fst (tgtC w))
bc-ty-c k u w e = trans (cong snd (bcell-at k u w e)) (bcR-ty-c k u w)

bc-dim : ∀ k u w → T (k <ℕ dimC u) → T (k <ℕ dimC w) → dimC (bcell k u w) ≡ max (dimC u) (dimC w)
bc-dim k u w p q = bcellR-dim (max (dimC u) (dimC w)) k u w refl p q

-- The type of a composite whose right factor is of top dimension
-- depends only on that factor's type.
par : ∀ k P ta tb A′ s u →
  btyR (suc (dim A′)) k P (ta , arr A′ s u) ≡ btyR (suc (dim A′)) k P (tb , arr A′ s u)
par k P ta tb A′ s u rewrite lt-irr (dim A′) = refl

private
  max-lt : ∀ a b → T (a <ℕ b) → max a b ≡ b
  max-lt zero    (suc b) _ = refl
  max-lt (suc a) (suc b) p = cong suc (max-lt a b p)

  max-le : ∀ a b → T (a <ℕ suc b) → max a b ≡ b
  max-le zero    b       _ = refl
  max-le (suc a) (suc b) p = cong suc (max-le a b p)
  max-le (suc a) zero    ()

  lt-ne′ : ∀ k a r′ → T (k <ℕ a) → T (a <ℕ suc r′) → (r′ ==ℕ k) ≡ false
  lt-ne′ zero    (suc a) zero    _ ()
  lt-ne′ zero    (suc a) (suc r′) _ _ = refl
  lt-ne′ (suc k) (suc a) zero    _ q = ⊥-elim (lt0 a q)
    where
    lt0 : ∀ a → T (a <ℕ 0) → ⊥
    lt0 _ ()
  lt-ne′ (suc k) (suc a) (suc r′) p q = lt-ne′ k a r′ p q

lo-keep : ∀ r c → T (dimC c <ℕ r) → loC r c ≡ c
lo-keep r c p rewrite T-true p = refl

hi-keep : ∀ r c → T (dimC c <ℕ r) → hiC r c ≡ c
hi-keep r c p rewrite T-true p = refl

lo-top : ∀ r c → dimC c ≡ r → loC r c ≡ srcC c
lo-top r c refl rewrite lt-irr (dimC c) = refl

hi-top : ∀ r c → dimC c ≡ r → hiC r c ≡ tgtC c
hi-top r c refl rewrite lt-irr (dimC c) = refl

-- A composite with a right factor of top dimension: its type depends
-- only on that factor's type.
par-bd : ∀ k P a b → snd a ≡ snd b → T (dimC P <ℕ suc (dimC a)) → T (0 <ℕ dimC a) →
         snd (bcell k P a) ≡ snd (bcell k P b)
par-bd k P (ta , arr A″ s u) (tb , .(arr A″ s u)) refl p _
  rewrite max-le (dimC P) (suc (dim A″)) p = par k P ta tb A″ s u

------------------------------------------------------------------------
-- Chains: P₁ ∗_{n−1} (P₂ ∗_{n−2} (… (Pₙ ∗₀ c))).

lenL : List Cell → Nat
lenL []       = 0
lenL (_ ∷ xs) = suc (lenL xs)

chainF : List Cell → Cell → Cell
chainF []       c = c
chainF (P ∷ Ps) c = bcell (lenL Ps) P (chainF Ps c)

-- Each factor's dimension lies strictly between its index and d.
ChainOK : List Cell → Nat → Set
ChainOK []       d = ⊤
ChainOK (P ∷ Ps) d = T (lenL Ps <ℕ dimC P) × T (dimC P <ℕ d) × ChainOK Ps d

chain-dim : ∀ Ps c → ChainOK Ps (dimC c) → dimC (chainF Ps c) ≡ dimC c
chain-dim []       c _ = refl
chain-dim (P ∷ Ps) c (p , q , ok) =
  trans (bc-dim (lenL Ps) P (chainF Ps c) p
                (subst (λ n → T (lenL Ps <ℕ n)) (sym ih) (lt-trans (lenL Ps) (dimC P) (dimC c) p q)))
        (trans (cong (max (dimC P)) ih) (max-lt (dimC P) (dimC c) q))
  where ih = chain-dim Ps c ok

private
  pos : ∀ a d → T (a <ℕ d) → Σ Nat (λ r′ → d ≡ suc r′)
  pos a (suc d) _ = d , refl
  pos zero    zero ()
  pos (suc a) zero ()

  lt-pos : ∀ k a r′ → T (k <ℕ a) → T (a <ℕ suc r′) → T (0 <ℕ r′)
  lt-pos k (suc a) (suc r′) _ _ = tt
  lt-pos k (suc a) zero p q = ⊥-elim (lt0 a q)
    where
    lt0 : ∀ a → T (a <ℕ 0) → ⊥
    lt0 _ ()
  lt-pos zero zero r′ () _
  lt-pos (suc k) zero r′ () _

-- A boundary of a chain whose factors all lie below the top is the
-- chain on the boundary (spec Lemma 2.2, the claim for j ≥ 2).
chain-src : ∀ Ps c → ChainOK Ps (dimC c) → srcC (chainF Ps c) ≡ chainF Ps (srcC c)
chain-src []       c _ = refl
chain-src (P ∷ Ps) c (p , q , ok) with pos (dimC P) (dimC c) q
... | r′ , ed =
  trans (bc-src-nc r′ k P V e1 ek)
        (cong₂ (bcell k) (lo-keep (suc r′) P (subst (λ n → T (dimC P <ℕ n)) ed q))
                         (trans (lo-top (suc r′) V (trans eV ed)) (chain-src Ps c ok)))
  where
  k = lenL Ps
  V = chainF Ps c
  eV = chain-dim Ps c ok
  e1 = trans (cong (max (dimC P)) eV) (trans (max-lt (dimC P) (dimC c) q) ed)
  ek = lt-ne′ k (dimC P) r′ p (subst (λ n → T (dimC P <ℕ n)) ed q)

chain-tgt : ∀ Ps c → ChainOK Ps (dimC c) → tgtC (chainF Ps c) ≡ chainF Ps (tgtC c)
chain-tgt []       c _ = refl
chain-tgt (P ∷ Ps) c (p , q , ok) with pos (dimC P) (dimC c) q
... | r′ , ed =
  trans (bc-tgt-nc r′ k P V e1 ek)
    (trans (cong₂ (λ X Y → (fst (bcell k X Y) , snd (bcell k (loC (suc r′) P) (loC (suc r′) V))))
                  (hi-keep (suc r′) P qr) (hi-top (suc r′) V eV′))
      (trans (cong₂ (λ X Y → (fst (bcell k P (tgtC V)) , snd (bcell k X Y)))
                    (lo-keep (suc r′) P qr) (lo-top (suc r′) V eV′))
        (trans (cong (λ Z → (fst (bcell k P (tgtC V)) , Z))
                     (par-bd k P (srcC V) (tgtC V) (src-tgt-type V)
                        (subst (λ n → T (dimC P <ℕ suc n)) (sym dsV) qr′)
                        (subst (λ n → T (0 <ℕ n)) (sym dsV) (lt-pos k (dimC P) r′ p qr))))
               (cong (bcell k P) (chain-tgt Ps c ok)))))
  where
  k = lenL Ps
  V = chainF Ps c
  eV = chain-dim Ps c ok
  eV′ = trans eV ed
  qr : T (dimC P <ℕ suc r′)
  qr = subst (λ n → T (dimC P <ℕ n)) ed q
  qr′ : T (dimC P <ℕ suc r′)
  qr′ = qr
  dsV : dimC (srcC V) ≡ r′
  dsV = trans (dim-src V) (cong pred eV′)
  e1 = trans (cong (max (dimC P)) eV) (trans (max-lt (dimC P) (dimC c) q) ed)
  ek = lt-ne′ k (dimC P) r′ p qr

-- Iterated boundaries.
srcN tgtN : Nat → Cell → Cell
srcN zero    c = c
srcN (suc n) c = srcN n (srcC c)
tgtN zero    c = c
tgtN (suc n) c = tgtN n (tgtC c)

dim-srcN : ∀ n c → dimC (srcN n c) ≡ dimC c ∸ n
dim-srcN zero    c = sym (∸-zero (dimC c))
  where
  ∸-zero : ∀ a → a ∸ 0 ≡ a
  ∸-zero zero    = refl
  ∸-zero (suc a) = refl
dim-srcN (suc n) c = trans (dim-srcN n (srcC c)) (trans (cong (_∸ n) (dim-src c)) (pred-∸ (dimC c) n))
  where
  pred-∸ : ∀ a n → pred a ∸ n ≡ a ∸ suc n
  pred-∸ zero    zero    = refl
  pred-∸ zero    (suc n) = refl
  pred-∸ (suc a) n       = refl

private
  lt0 : ∀ a → T (a <ℕ 0) → ⊥
  lt0 _ ()

  -- ChainOK is monotone in its bound.
  lt-mono : ∀ a d d′ → T (a <ℕ d) → T (d <ℕ suc d′) → T (a <ℕ d′)
  lt-mono zero    (suc d) (suc d′) _ _ = tt
  lt-mono zero    (suc d) zero     _ q = ⊥-elim (lt0 d q)
  lt-mono (suc a) (suc d) (suc d′) p q = lt-mono a d d′ p q
  lt-mono (suc a) (suc d) zero     _ q = ⊥-elim (lt0 d q)

chainOK-mono : ∀ Ps d d′ → ChainOK Ps d → T (d <ℕ suc d′) → ChainOK Ps d′
chainOK-mono []       d d′ _ _ = tt
chainOK-mono (P ∷ Ps) d d′ (p , q , ok) r = p , lt-mono (dimC P) d d′ q r , chainOK-mono Ps d d′ ok r

private
  -- suc (a ∸ suc n) ≤ a when n < a.
  le-∸ : ∀ a n → T (n <ℕ a) → T (suc (a ∸ suc n) <ℕ suc a)
  le-∸ (suc a) zero    _ = lt-suc′ a
    where
    lt-suc′ : ∀ a → T (a <ℕ suc a)
    lt-suc′ zero    = tt
    lt-suc′ (suc a) = lt-suc′ a
  le-∸ (suc a) (suc n) p = le-∸′ a n p
    where
    le-∸′ : ∀ a n → T (n <ℕ a) → T (suc (a ∸ suc n) <ℕ suc (suc a))
    le-∸′ a n p = lt-trans (suc (a ∸ suc n)) (suc a) (suc (suc a)) (le-∸ a n p) (lt-suc (suc a))

  pred-∸′ : ∀ a n → pred a ∸ n ≡ a ∸ suc n
  pred-∸′ zero    zero    = refl
  pred-∸′ zero    (suc n) = refl
  pred-∸′ (suc a) n       = refl

  n<pred : ∀ n a → T (suc n <ℕ suc a) → T (n <ℕ suc (pred a))
  n<pred n (suc a) p = p
  n<pred n zero p = ⊥-elim (lt0 n p)

-- Iterated sources of a chain whose factors stay below.
chain-srcN : ∀ n Ps c → T (n <ℕ suc (dimC c)) → ChainOK Ps (suc (dimC c ∸ n)) →
             srcN n (chainF Ps c) ≡ chainF Ps (srcN n c)
chain-srcN zero    Ps c _ _  = refl
chain-srcN (suc n) Ps c p ok =
  trans (cong (srcN n) (chain-src Ps c (chainOK-mono Ps _ (dimC c) ok (le-∸ (dimC c) n p))))
        (chain-srcN n Ps (srcC c)
          (subst (λ d → T (n <ℕ suc d)) (sym (dim-src c)) (n<pred n (dimC c) p))
          (subst (λ d → ChainOK Ps (suc d))
                 (sym (trans (cong (_∸ n) (dim-src c)) (pred-∸′ (dimC c) n))) ok))

------------------------------------------------------------------------
-- The specified cone (Mikhail, Thm 3.3), with apex `apex` and the
-- projection of the variable named i named `pn i`.

module Proj (apex : Nat) (pn : Nat → Nat) where
  pv : Tm → Tm
  pv (var i) = var (pn i)
  pv _       = var apex

  mutual
    -- The type of p_x, for x : A.
    projN : Tm → Ty → Ty
    projN x ⋆           = arr ⋆ (var apex) x
    projN x (arr B s t) = arr (projN t B) (pv t) (fst (chainF (pcs (arr B s t)) (x , arr B s t)))

    -- p_{σt}, p_{σ²t}, …, p_{σᵐt} for t : A.
    pcs : Ty → List Cell
    pcs ⋆           = []
    pcs (arr B s t) = (pv s , projN s B) ∷ pcs B

  -- p_x as a cell.
  pc : Cell → Cell
  pc (x , A) = pv x , projN x A

  -- T_x = p_{σx} ∗_{m−1} (… (p_{σᵐx} ∗₀ x)).
  Tc : Cell → Cell
  Tc (x , A) = chainF (pcs A) (x , A)

  dim-projN : ∀ x A → dim (projN x A) ≡ suc (dim A)
  dim-projN x ⋆           = refl
  dim-projN x (arr B s t) = cong suc (dim-projN t B)

  len-pcs : ∀ A → lenL (pcs A) ≡ dim A
  len-pcs ⋆           = refl
  len-pcs (arr B s t) = cong suc (len-pcs B)

  pcs-ok : ∀ B d → T (dim B <ℕ d) → ChainOK (pcs B) d
  pcs-ok ⋆           d _ = tt
  pcs-ok (arr B s t) d p =
    subst (λ n → T (n <ℕ dim (projN s B))) (sym (len-pcs B))
          (subst (λ n → T (dim B <ℕ n)) (sym (dim-projN s B)) (lt-suc (dim B)))
    , subst (λ n → T (n <ℕ d)) (sym (dim-projN s B)) p
    , pcs-ok B d (lt-trans (dim B) (suc (dim B)) d (lt-suc (dim B)) p)

  private
    fin : ∀ s t B → arr (snd (srcC (pv s , projN s B))) (fst (srcC (pv s , projN s B))) (fst (Tc (t , B)))
                    ≡ projN t B
    fin s t ⋆              = refl
    fin s t (arr B′ s′ t′) = refl

  chain-ok : ∀ B s t x → ChainOK (pcs B) (dimC (x , arr B s t))
  chain-ok B s t x = pcs-ok B (suc (dim B)) (lt-suc (dim B))

  -- T_t has the type of p_{τt} (spec Lemma 2.2, the case j = 1): the
  -- type of p_t is well formed.
  T-par : ∀ x B s t → snd (Tc (x , arr B s t)) ≡ projN t B
  T-par x B s t =
    trans (bc-ty-c (lenL (pcs B)) P V e)
      (trans (cong (λ Z → arr (snd (srcC P)) (fst (srcC P)) (fst Z)) (chain-tgt (pcs B) c (chain-ok B s t x)))
             (fin s t B))
    where
    c = (x , arr B s t)
    P = (pv s , projN s B)
    V = chainF (pcs B) c
    e : max (dimC P) (dimC V) ≡ suc (lenL (pcs B))
    e = trans (cong₂ max (dim-projN s B) (chain-dim (pcs B) c (chain-ok B s t x)))
              (trans (max-idem (suc (dim B))) (cong suc (sym (len-pcs B))))

  -- The target of p_t is T_t.
  tgt-pc : ∀ c → tgtC (pc c) ≡ Tc c
  tgt-pc (x , ⋆)       = refl
  tgt-pc (x , arr B s t) = cong (fst (Tc (x , arr B s t)) ,_) (sym (T-par x B s t))

  -- Composability (spec Lemma 2.2): in T_t, the factor p_u with
  -- u = σⁿt meets the inner chain V along dimension dim u; the target of
  -- p_u is the n-fold source of V.
  chain-comp : ∀ n c → T (n <ℕ suc (dimC c)) →
    tgtC (pc (srcN n c)) ≡ srcN n (chainF (pcs (snd (srcN n c))) c)
  chain-comp n c p =
    trans (tgt-pc (srcN n c))
      (sym (chain-srcN n (pcs (snd (srcN n c))) c p
             (pcs-ok (snd (srcN n c)) (suc (dimC c ∸ n))
                     (subst (λ d → T (d <ℕ suc (dimC c ∸ n))) (sym (dim-srcN n c)) (lt-suc (dimC c ∸ n))))))
