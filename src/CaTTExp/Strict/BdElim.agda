------------------------------------------------------------------------
-- Boundary elimination for expressions (ledger A5, existence half of
-- N2, step L1).
--
-- Fix, for every generator g, composition-only expressions W σ⁻ g and
-- W σ⁺ g in generators of degree < deg g (the outside response's
-- attaching words (19)). Then the n-source and n-target of any
-- composition-only expression are again composition-only expressions,
-- in generators of degree ≤ n:
--   bd s f n e      (s = σ⁻ or σ⁺, f a degree bound for e).
-- `bd` is syntax only. `Sem.sound` shows it is correct in every strict
-- ω-category 𝒞 whose generator values have dimension deg g and whose
-- boundaries are the values of the words W. The same expression works
-- in ν(K) and in the target category at once.
------------------------------------------------------------------------
module CaTTExp.Strict.BdElim where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Expr

data Sd : Set where
  σ⁻ σ⁺ : Sd

module Syn {G : Set} (deg : G → Nat) (W : Sd → G → Expr G) where

  -- Composition-only expressions.
  data CO : Expr G → Set where
    co-gen : ∀ g → CO (gen g)
    co-cmp : ∀ n {e e′} → CO e → CO e′ → CO (cmp n e e′)

  -- All generators have degree ≤ d.
  data DegLe (d : Nat) : Expr G → Set where
    dl-gen : ∀ {g} → deg g ≤ d → DegLe d (gen g)
    dl-cmp : ∀ {n e e′} → DegLe d e → DegLe d e′ → DegLe d (cmp n e e′)

  DegLe-mono : ∀ {d d′ e} → d ≤ d′ → DegLe d e → DegLe d′ e
  DegLe-mono l (dl-gen p)   = dl-gen (≤-trans p l)
  DegLe-mono l (dl-cmp a b) = dl-cmp (DegLe-mono l a) (DegLe-mono l b)

  mutual
    bd : Sd → Nat → Nat → Expr G → Expr G
    bd s f n (gen g)      = bdg s f n g (tri (deg g) n)
    bd s f n (cmp k e e′) = bdc s f n k e e′ (tri n k)
    bd s f n e            = e

    bdg : Sd → Nat → (n : Nat) (g : G) → Tri (deg g) n → Expr G
    bdg s f       n g (tri< _) = gen g
    bdg s f       n g (tri≡ _) = gen g
    bdg s zero    n g (tri> _) = gen g
    bdg s (suc f) n g (tri> _) = bd s f n (W s g)

    bdc : Sd → Nat → (n k : Nat) → Expr G → Expr G → Tri n k → Expr G
    bdc s f n k e e′ (tri> _) = cmp k (bd s f n e) (bd s f n e′)
    bdc σ⁻ f n k e e′ (tri< _) = bd σ⁻ f n e
    bdc σ⁺ f n k e e′ (tri< _) = bd σ⁺ f n e′
    bdc σ⁻ f n k e e′ (tri≡ _) = bd σ⁻ f n e
    bdc σ⁺ f n k e e′ (tri≡ _) = bd σ⁺ f n e′

  ----------------------------------------------------------------------
  -- Syntactic properties, given the words are composition-only and of
  -- lower degree.

  module Props (W-co : ∀ s g → CO (W s g))
               (W-deg : ∀ s g → DegLe (deg g ∸ 1) (W s g)) where

    private
      pred≤ : ∀ {n d f} → n < d → d ≤ suc f → d ∸ 1 ≤ f
      pred≤ {d = suc d} _ (s≤s l) = l

      <→pred : ∀ {n d} → n < d → n ≤ d ∸ 1
      <→pred {d = suc d} (s≤s l) = l

    mutual
      bd-co : ∀ s f n e → CO e → CO (bd s f n e)
      bd-co s f n (gen g)      _              = bdg-co s f n g (tri (deg g) n)
      bd-co s f n (cmp k e e′) (co-cmp _ a b) = bdc-co s f n k e e′ a b (tri n k)

      bdg-co : ∀ s f n g (t : Tri (deg g) n) → CO (bdg s f n g t)
      bdg-co s f       n g (tri< _) = co-gen g
      bdg-co s f       n g (tri≡ _) = co-gen g
      bdg-co s zero    n g (tri> _) = co-gen g
      bdg-co s (suc f) n g (tri> _) = bd-co s f n (W s g) (W-co s g)

      bdc-co : ∀ s f n k e e′ → CO e → CO e′ → (t : Tri n k) → CO (bdc s f n k e e′ t)
      bdc-co σ⁻ f n k e e′ a b (tri< _) = bd-co σ⁻ f n e a
      bdc-co σ⁺ f n k e e′ a b (tri< _) = bd-co σ⁺ f n e′ b
      bdc-co σ⁻ f n k e e′ a b (tri≡ _) = bd-co σ⁻ f n e a
      bdc-co σ⁺ f n k e e′ a b (tri≡ _) = bd-co σ⁺ f n e′ b
      bdc-co s f n k e e′ a b (tri> _) = co-cmp k (bd-co s f n e a) (bd-co s f n e′ b)

    -- The result has generators of degree ≤ n.
    mutual
      bd-deg : ∀ s f n e → DegLe f e → DegLe n (bd s f n e)
      bd-deg s f n (gen g)      (dl-gen l)   = bdg-deg s f n g l (tri (deg g) n)
      bd-deg s f n (cmp k e e′) (dl-cmp a b) = bdc-deg s f n k e e′ a b (tri n k)

      bdg-deg : ∀ s f n g → deg g ≤ f → (t : Tri (deg g) n) → DegLe n (bdg s f n g t)
      bdg-deg s f       n g l (tri< p) = dl-gen (<→≤ p)
      bdg-deg s f       n g l (tri≡ p) = dl-gen (subst (_≤ n) (sym p) (≤-refl n))
      bdg-deg s zero    n g l (tri> p) = ⊥-elim (absurd l p)
        where
        absurd : ∀ {d} → d ≤ zero → n < d → ⊥
        absurd z≤n ()
      bdg-deg s (suc f) n g l (tri> p) = bd-deg s f n (W s g) (DegLe-mono (pred≤ p l) (W-deg s g))

      bdc-deg : ∀ s f n k e e′ → DegLe f e → DegLe f e′ → (t : Tri n k) → DegLe n (bdc s f n k e e′ t)
      bdc-deg σ⁻ f n k e e′ a b (tri< _) = bd-deg σ⁻ f n e a
      bdc-deg σ⁺ f n k e e′ a b (tri< _) = bd-deg σ⁺ f n e′ b
      bdc-deg σ⁻ f n k e e′ a b (tri≡ _) = bd-deg σ⁻ f n e a
      bdc-deg σ⁺ f n k e e′ a b (tri≡ _) = bd-deg σ⁺ f n e′ b
      bdc-deg s f n k e e′ a b (tri> _) = dl-cmp (bd-deg s f n e a) (bd-deg s f n e′ b)

  ----------------------------------------------------------------------
  -- Correctness in a strict ω-category.

  module Sem (𝒞 : ωCat) (ι : G → ωCat.C 𝒞) where
    open ωCat 𝒞
    open Eval 𝒞 ι

    bdC : Sd → Nat → C → C
    bdC σ⁻ = src
    bdC σ⁺ = tgt

    module _ (W-deg : ∀ s g → DegLe (deg g ∸ 1) (W s g))
             (dimι : ∀ g → src (deg g) (ι g) ≡ ι g)
             (W-ev : ∀ s g → 1 ≤ deg g → Ev (W s g) (bdC s (deg g ∸ 1) (ι g))) where

      private
        -- A generator's value is its own n-boundary for n ≥ its degree.
        gen-bd : ∀ s g n → deg g ≤ n → bdC s n (ι g) ≡ ι g
        gen-bd σ⁻ g n l = trans (cong (src n) (sym (dimι g))) (trans (src-src-≥ (ι g) l) (dimι g))
        gen-bd σ⁺ g n l = trans (cong (tgt n) (sym (dimι g))) (trans (tgt-src-≥ (ι g) l) (dimι g))

        -- Iterated boundaries on the same side.
        bb : ∀ s {n m} x → n ≤ m → bdC s n (bdC s m x) ≡ bdC s n x
        bb s {n} {m} x l with tri n m
        bb σ⁻ x l | tri< p = src-src-< x p
        bb σ⁺ x l | tri< p = tgt-tgt-< x p
        bb σ⁻ x l | tri≡ refl = src-src-≥ x l
        bb σ⁺ x l | tri≡ refl = tgt-tgt-≥ x l
        bb s x l | tri> p = ⊥-elim (≤-<-⊥ l p)

        <→pred : ∀ {n d} → n < d → n ≤ d ∸ 1
        <→pred {d = suc d} (s≤s l) = l

        one≤ : ∀ {n d} → n < d → 1 ≤ d
        one≤ {d = suc d} _ = s≤s z≤n

        -- Boundary of a composite along a lower dimension.
        cmp-q : ∀ s {k n} x y → k < n → tgt k x ≡ src k y → tgt k (bdC s n x) ≡ src k (bdC s n y)
        cmp-q σ⁻ x y l p = trans (tgt-src-< x l) (trans p (sym (src-src-< y l)))
        cmp-q σ⁺ x y l p = trans (tgt-tgt-< x l) (trans p (sym (src-tgt-< y l)))

        cmp-hi : ∀ s {k n} x y p → k < n → (q : tgt k (bdC s n x) ≡ src k (bdC s n y)) →
                 bdC s n (comp k x y p) ≡ comp k (bdC s n x) (bdC s n y) q
        cmp-hi σ⁻ x y p l q = src-comp-> x y p l q
        cmp-hi σ⁺ x y p l q = tgt-comp-> x y p l q

      mutual
        sound : ∀ s f n e {x} → DegLe f e → Ev e x → Ev (bd s f n e) (bdC s n x)
        sound s f n (gen g)      (dl-gen l)   (ev-gen .g)      = soundg s f n g l (tri (deg g) n)
        sound s f n (cmp k e e′) (dl-cmp a b) (ev-cmp .k u v p) = soundc s f n k e e′ a b u v p (tri n k)

        soundg : ∀ s f n g → deg g ≤ f → (t : Tri (deg g) n) → Ev (bdg s f n g t) (bdC s n (ι g))
        soundg s f n g l (tri< p) = subst (Ev (gen g)) (sym (gen-bd s g n (<→≤ p))) (ev-gen g)
        soundg s f n g l (tri≡ p) =
          subst (Ev (gen g)) (sym (gen-bd s g n (subst (_≤ n) (sym p) (≤-refl n)))) (ev-gen g)
        soundg s zero n g l (tri> p) = ⊥-elim (absurd l p)
          where
          absurd : ∀ {d} → d ≤ zero → n < d → ⊥
          absurd z≤n ()
        soundg s (suc f) n g l (tri> p) =
          subst (Ev (bd s f n (W s g))) (bb s (ι g) (<→pred p))
            (sound s f n (W s g) (DegLe-mono (pred≤ p l) (W-deg s g)) (W-ev s g (one≤ p)))
          where
          pred≤ : ∀ {n d f} → n < d → d ≤ suc f → d ∸ 1 ≤ f
          pred≤ {d = suc d} _ (s≤s l′) = l′

        soundc : ∀ s f n k e e′ → DegLe f e → DegLe f e′ → ∀ {x y} → Ev e x → Ev e′ y →
                 (p : tgt k x ≡ src k y) → (t : Tri n k) →
                 Ev (bdc s f n k e e′ t) (bdC s n (comp k x y p))
        soundc σ⁻ f n k e e′ a b {x} {y} u v p (tri< l) =
          subst (Ev (bd σ⁻ f n e)) (sym (src-comp-< x y p l)) (sound σ⁻ f n e a u)
        soundc σ⁺ f n k e e′ a b {x} {y} u v p (tri< l) =
          subst (Ev (bd σ⁺ f n e′)) (sym (tgt-comp-< x y p l)) (sound σ⁺ f n e′ b v)
        soundc σ⁻ f n k e e′ a b {x} {y} u v p (tri≡ refl) =
          subst (Ev (bd σ⁻ f n e)) (sym (src-comp n x y p)) (sound σ⁻ f n e a u)
        soundc σ⁺ f n k e e′ a b {x} {y} u v p (tri≡ refl) =
          subst (Ev (bd σ⁺ f n e′)) (sym (tgt-comp n x y p)) (sound σ⁺ f n e′ b v)
        soundc s f n k e e′ a b {x} {y} u v p (tri> l) =
          subst (Ev (cmp k (bd s f n e) (bd s f n e′))) (sym (cmp-hi s x y p l q))
            (ev-cmp k (sound s f n e a u) (sound s f n e′ b v) q)
          where
          q = cmp-q s x y l p
