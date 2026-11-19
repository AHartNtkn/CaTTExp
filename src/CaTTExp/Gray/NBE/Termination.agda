------------------------------------------------------------------------
-- Termination of N/β/η (D18, §1.3 of the 2026-11-19 answer).
--
-- Measure: μ(w) = (n(w), pot_{n(w)}(w)) in lexicographic order, where
-- n counts primitive nodes (generators, evaluations, curries) and
--
--     pot_B(w) = Σ_{nodes v} (B − depth v),
--
-- depth counting enclosing curries.  β and η delete a curry and an
-- evaluation, so n drops by 2.  N keeps n and pushes one triple's
-- subtree one level deeper; while B ≥ n every node has depth < B, so
-- pot_B drops by the size of that subtree.  This replaces the paper's
-- second coordinate C(n,2) − a by an equivalent depth potential that
-- is compositional.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Termination (Fac G : Set) where

open import CaTTExp.Gray.NBE.Base
open import CaTTExp.Gray.NBE.Syntax Fac G

mutual
  sizeP : Prim → Nat
  sizeP (gen _)       = 1
  sizeP (ev _ _ _)    = 1
  sizeP (cur _ _ _ b) = suc (sizeW b)

  sizeT : Triple → Nat
  sizeT (tri _ q _) = sizeP q

  sizeW : Word → Nat
  sizeW []      = 0
  sizeW (t ∷ w) = sizeT t + sizeW w

mutual
  potP : Nat → Prim → Nat
  potP B (gen _)       = B
  potP B (ev _ _ _)    = B
  potP B (cur _ _ _ b) = B + potW (pred B) b

  potT : Nat → Triple → Nat
  potT B (tri _ q _) = potP B q

  potW : Nat → Word → Nat
  potW B []      = 0
  potW B (t ∷ w) = potT B t + potW B w

------------------------------------------------------------------------
-- Basic facts

sizeP-pos : ∀ q → 1 ≤ sizeP q
sizeP-pos (gen _)       = s≤s z≤n
sizeP-pos (ev _ _ _)    = s≤s z≤n
sizeP-pos (cur _ _ _ b) = s≤s z≤n

sizeP-suc : ∀ q → Σ Nat (λ s → sizeP q ≡ suc s)
sizeP-suc (gen _)       = 0 , refl
sizeP-suc (ev _ _ _)    = 0 , refl
sizeP-suc (cur _ _ _ b) = sizeW b , refl

sizeW-++ : ∀ xs ys → sizeW (xs ++ ys) ≡ sizeW xs + sizeW ys
sizeW-++ []       ys = refl
sizeW-++ (x ∷ xs) ys =
  trans (cong (sizeT x +_) (sizeW-++ xs ys)) (sym (+-assoc (sizeT x) (sizeW xs) (sizeW ys)))

sizeW-ctx : ∀ P S g → sizeW (map (inCtx P S) g) ≡ sizeW g
sizeW-ctx P S []              = refl
sizeW-ctx P S (tri l q r ∷ g) = cong (sizeP q +_) (sizeW-ctx P S g)

-- The potential gains exactly the size when the base grows by one,
-- as long as the base bounds the size.
mutual
  potP-suc : ∀ B q → sizeP q ≤ B → potP (suc B) q ≡ potP B q + sizeP q
  potP-suc B (gen _)    _ = sym (trans (+-suc B 0) (cong suc (+-identityʳ B)))
  potP-suc B (ev _ _ _) _ = sym (trans (+-suc B 0) (cong suc (+-identityʳ B)))
  potP-suc (suc B) (cur _ _ _ b) (s≤s p) =
    -- suc (suc B) + potW (suc B) b ≡ (suc B + potW B b) + suc (sizeW b)
    trans (cong (λ x → suc (suc B) + x) (potW-suc B b p))
   (sym (trans (+-suc (suc B + potW B b) (sizeW b))
         (cong suc (+-assoc (suc B) (potW B b) (sizeW b)))))

  potW-suc : ∀ B w → sizeW w ≤ B → potW (suc B) w ≡ potW B w + sizeW w
  potW-suc B []              _ = refl
  potW-suc B (tri l q r ∷ w) p =
    trans (cong₂ _+_ (potP-suc B q (≤-+ˡ (sizeP q) (sizeW w) p))
                     (potW-suc B w (≤-+ʳ (sizeP q) (sizeW w) p)))
          (+-interchange (potP B q) (sizeP q) (potW B w) (sizeW w))

------------------------------------------------------------------------
-- Each step decreases the measure

Decr : Word → Word → Set
Decr w w' = (sizeW w' < sizeW w)
          ⊎ (sizeW w' ≡ sizeW w × (∀ B → sizeW w ≤ B → potW B w' < potW B w))

-- N: equal size, and the absorbed triple's potential drops by its size.
N-size : ∀ x y z → x + (suc y + z) ≡ suc (x + y) + z
N-size x y z = trans (cong (x +_) (sym (+-suc y z)))
              (trans (sym (+-assoc x y (suc z)))
              (trans (+-suc (x + y) z) refl))

N-pot : ∀ x s B y z → (B + (x + y)) + z < (x + suc s) + ((B + y) + z)
N-pot x s B y z =
  subst (λ k → suc ((B + (x + y)) + z) ≤ k) (sym eq)
        (s≤s (m≤m+n ((B + (x + y)) + z) s))
  where
    -- (x + suc s) + ((B + y) + z) ≡ suc (((B + (x + y)) + z) + s)
    eq : (x + suc s) + ((B + y) + z) ≡ suc (((B + (x + y)) + z) + s)
    eq =
      trans (cong (_+ ((B + y) + z)) (+-suc x s))
     (cong suc
      (trans (cong (_+ ((B + y) + z)) (+-comm x s))
      (trans (+-assoc s x ((B + y) + z))
      (trans (+-comm s (x + ((B + y) + z)))
      (cong (_+ s)
        (trans (sym (+-assoc x (B + y) z))
        (cong (_+ z)
          (trans (sym (+-assoc x B y))
          (trans (cong (_+ y) (+-comm x B))
                 (+-assoc B x y))))))))))

step-decr : ∀ {w w'} → w ⟶ w' → Decr w w'
step-decr (N {DL} {DR} {CL} {CR} {D0L} {D0R} {q} {d} {A} {Z} {b} {w} _ _) =
  inr (sym (N-size (sizeP q) (sizeW b) (sizeW w)) , pot)
  where
    pot : ∀ B → sizeP q + (suc (sizeW b) + sizeW w) ≤ B
        → potW B (tri CL (cur d A Z (wrap d A (tri D0L q D0R) ∷ b)) CR ∷ w)
          < potW B (tri DL q DR ∷ tri CL (cur d A Z b) CR ∷ w)
    pot zero p with sizeP-suc q
    ... | (s , e) with subst (λ k → k + (suc (sizeW b) + sizeW w) ≤ zero) e p
    ... | ()
    pot (suc B) p with sizeP-suc q
    ... | (s , e) =
      subst (λ k → (suc B + (potP B q + potW B b)) + potW (suc B) w
                   < k + ((suc B + potW B b) + potW (suc B) w))
            (trans (cong (potP B q +_) (sym e)) (sym (potP-suc B q bound)))
            (N-pot (potP B q) s (suc B) (potW B b) (potW (suc B) w))
      where
        bound : sizeP q ≤ B
        bound = ≤-+ˡ (sizeP q) (sizeW b + sizeW w)
                  (≤-pred (subst (λ k → k ≤ suc B)
                     (+-suc (sizeP q) (sizeW b + sizeW w)) p))
step-decr (β {CL = CL} {CR = CR} {b = b} {w = w} _ _) =
  inl (subst (λ k → suc k ≤ suc (sizeW b) + suc (sizeW w))
             (sym (trans (sizeW-++ (map (inCtx CL CR) b) w)
                         (cong (_+ sizeW w) (sizeW-ctx CL CR b))))
             (s≤s (subst (λ k → sizeW b + sizeW w ≤ k)
                         (sym (+-suc (sizeW b) (sizeW w)))
                         (≤-step ≤-refl))))
step-decr (η {CL = CL} {CR = CR} {d = d} {A = A} {Z = Z} {g = g} {w = w} refl) =
  inl (subst (λ k → suc k ≤ suc (sizeW (map (wrap d A) g ++ (evT d A Z ∷ []))) + sizeW w)
             (sym (trans (sizeW-++ (map (inCtx CL CR) g) w)
                         (cong (_+ sizeW w) (sizeW-ctx CL CR g))))
             (s≤s (+-monoˡ-≤ (sizeW w)
               (subst (λ k → sizeW g ≤ k)
                      (sym (trans (sizeW-++ (map (wrap d A) g) (evT d A Z ∷ []))
                           (trans (cong (_+ 1) (sizeW-ctx (pre d A) (post d A) g))
                                  (+-comm (sizeW g) 1))))
                      (≤-step ≤-refl)))))
step-decr (skip {t = t} s) with step-decr s
... | inl p = inl (+-monoʳ-< (sizeT t) p)
... | inr (e , f) =
  inr (cong (sizeT t +_) e ,
       λ B p → +-monoʳ-< (potT B t) (f B (≤-+ʳ (sizeT t) _ p)))
step-decr (body {b = b} {b' = b'} {w = w} s) with step-decr s
... | inl p = inl (+-monoˡ-< (sizeW w) (s≤s p))
... | inr (e , f) =
  inr (cong (λ k → suc k + sizeW w) e , pot)
  where
    pot : ∀ B → suc (sizeW b) + sizeW w ≤ B
        → (B + potW (pred B) b') + potW B w < (B + potW (pred B) b) + potW B w
    pot (suc B) p =
      +-monoˡ-< (potW (suc B) w)
        (+-monoʳ-< (suc B) (f B (≤-pred (≤-+ˡ (suc (sizeW b)) (sizeW w) p))))

------------------------------------------------------------------------
-- Strong normalisation

μ : Word → Nat × Nat
μ w = (sizeW w , potW (sizeW w) w)

μ-decr : ∀ {w w'} → w ⟶ w' → μ w' <lex μ w
μ-decr {w} {w'} s with step-decr s
... | inl p = fst< p
... | inr (e , f) =
  subst (λ n → (n , potW n w') <lex (sizeW w , potW (sizeW w) w)) (sym e)
        (snd< (f (sizeW w) ≤-refl))

sn : ∀ w → SN w
sn w = go (μ w) (lex-wf (μ w)) w refl
  where
    go : ∀ p → Acc _<lex_ p → ∀ w → μ w ≡ p → SN w
    go p (acc r) w refl = acc λ v s → go (μ v) (r (μ v) (μ-decr s)) v refl
