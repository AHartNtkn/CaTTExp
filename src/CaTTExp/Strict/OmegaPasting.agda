------------------------------------------------------------------------
-- Pasting composites in a strict ω-category (ledger item A3a, general
-- case; plan in notes/strict-omega-soundness.md §4, steps 1–3).
--
-- A labelled Batanin tree at level k is `node x₀ [(T₁, x₁) … (Tₘ, xₘ)]`:
-- the xᵢ are the k-cells along the spine and Tᵢ is a labelled tree at
-- level k+1 whose spine runs between parallel (k+1)-cells from x_{i−1}
-- to xᵢ. Its composite is the fold
--
--     comp (node x₀ [])              = x₀
--     comp (node x₀ ((T, x) ∷ rest)) = comp T #ₖ comp (node x rest).
--
-- Composition is partial, so the composite is a relation `Cp k T c`,
-- whose constructors carry the boundary conditions (the labelling is
-- valid) and the composability proofs. It is deterministic (`cp-det`).
--
-- Proved here, from the axioms of Strict.Omega:
--   * boundary lemma: s_j and t_j of a composite are the composites of
--     the truncations of the tree at height j (`cp-src`, `cp-tgt`);
--   * binary pasting lemma: the composite of two trees glued along
--     their common j-boundary is the #_j-composite of their composites
--     (`cp-glue`). The j = k case is associativity, the j > k case is
--     interchange of #ₖ with #_j, folded along the spine.
------------------------------------------------------------------------
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.OmegaPasting (𝒞 : ωCat) where

open import CaTTExp.Prelude
open ωCat 𝒞
open Basics 𝒞

------------------------------------------------------------------------
-- Labelled trees.

mutual
  data LT : Set where
    node : C → Br → LT

  data Br : Set where
    nil  : Br
    cons : LT → C → Br → Br

lastv : C → Br → C
lastv x nil          = x
lastv x (cons _ y r) = lastv y r

infixr 5 _++B_
_++B_ : Br → Br → Br
nil          ++B r′ = r′
cons T y r   ++B r′ = cons T y (r ++B r′)

private
  rootLT : LT → C
  rootLT (node x _) = x

  kidsLT : LT → Br
  kidsLT (node _ r) = r

  hdB : LT → Br → LT
  hdB d nil          = d
  hdB d (cons T _ _) = T

  vB : C → Br → C
  vB d nil          = d
  vB d (cons _ y _) = y

  tlB : Br → Br
  tlB nil          = nil
  tlB (cons _ _ r) = r

  ==→≡ : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
  ==→≡ m n e = ==ℕ-sound m n (subst T (sym e) tt)

  ≤-≢→< : ∀ {k j} → k ≤ j → (j ==ℕ k) ≡ false → k < j
  ≤-≢→< {zero}  {zero}  z≤n     ()
  ≤-≢→< {zero}  {suc j} z≤n     _ = s≤s z≤n
  ≤-≢→< {suc k} {suc j} (s≤s p) e = s≤s (≤-≢→< p e)

------------------------------------------------------------------------
-- Composites.

mutual
  data Cp (k : Nat) : LT → C → Set where
    cp : ∀ {x r c} → CpB k x r c → Cp k (node x r) c

  -- CpB k x r c: the spine starting at x with branches r composes to c.
  data CpB (k : Nat) : C → Br → C → Set where
    cnil  : ∀ {x} → Dim≤ k x → CpB k x nil x
    ccons : ∀ {x T y r a b} → Cp (suc k) T a → src k a ≡ x → CpB k y r b →
            (p : tgt k a ≡ src k b) → CpB k x (cons T y r) (comp k a b p)

cpB-src : ∀ {k x r c} → CpB k x r c → src k c ≡ x
cpB-src (cnil d) = d
cpB-src {k} (ccons {a = a} {b = b} _ e _ p) = trans (src-comp k a b p) e

cpB-tgt : ∀ {k x r c} → CpB k x r c → tgt k c ≡ lastv x r
cpB-tgt (cnil d) = tgt-of-dim d
cpB-tgt {k} (ccons {a = a} {b = b} _ _ cb p) = trans (tgt-comp k a b p) (cpB-tgt cb)

mutual
  cp-det : ∀ {k T c c′} → Cp k T c → Cp k T c′ → c ≡ c′
  cp-det (cp u) (cp v) = cpB-det u v

  cpB-det : ∀ {k x r c c′} → CpB k x r c → CpB k x r c′ → c ≡ c′
  cpB-det (cnil _) (cnil _) = refl
  cpB-det {k} (ccons ca _ cb p) (ccons ca′ _ cb′ p′) = comp-cong k p p′ (cp-det ca ca′) (cpB-det cb cb′)

------------------------------------------------------------------------
-- Truncation at absolute height j (the tree being at level k ≤ j).

mutual
  bdm : Nat → Nat → LT → LT
  bdm j k (node x r) with j ==ℕ k
  ... | true  = node x nil
  ... | false = node x (bdmB j (suc k) r)

  bdmB : Nat → Nat → Br → Br
  bdmB j k nil          = nil
  bdmB j k (cons T y r) = cons (bdm j k T) y (bdmB j k r)

mutual
  bdp : Nat → Nat → LT → LT
  bdp j k (node x r) with j ==ℕ k
  ... | true  = node (lastv x r) nil
  ... | false = node x (bdpB j (suc k) r)

  bdpB : Nat → Nat → Br → Br
  bdpB j k nil          = nil
  bdpB j k (cons T y r) = cons (bdp j k T) y (bdpB j k r)

------------------------------------------------------------------------
-- Boundary lemma.

mutual
  cp-src : ∀ j k {T c} → k ≤ j → Cp k T c → Cp k (bdm j k T) (src j c)
  cp-src j k {node x r} {c} le (cp u) with j ==ℕ k in e
  ... | true with ==→≡ j k e
  ...   | refl = cp (subst (λ z → CpB k z nil (src k c)) (cpB-src u) (cnil (src-dim k c)))
  cp-src j k {node x r} le (cp u) | false = cp (srcB j k (≤-≢→< le e) u)

  srcB : ∀ j k {x r c} → k < j → CpB k x r c → CpB k x (bdmB j (suc k) r) (src j c)
  srcB j k lt (cnil {x} d) = subst (CpB k x nil) (sym (dim-up (<→≤ lt) d)) (cnil d)
  srcB j k {x} lt (ccons {T = T} {y} {r} {a} {b} ca e cb p) =
    subst (CpB k x (cons (bdm j (suc k) T) y (bdmB j (suc k) r))) (sym (src-comp-> a b p lt q))
      (ccons (cp-src j (suc k) lt ca) (trans (src-src-< a lt) e) (srcB j k lt cb) q)
    where
    q : tgt k (src j a) ≡ src k (src j b)
    q = trans (tgt-src-< a lt) (trans p (sym (src-src-< b lt)))

mutual
  cp-tgt : ∀ j k {T c} → k ≤ j → Cp k T c → Cp k (bdp j k T) (tgt j c)
  cp-tgt j k {node x r} {c} le (cp u) with j ==ℕ k in e
  ... | true with ==→≡ j k e
  ...   | refl = cp (subst (λ z → CpB k z nil (tgt k c)) (cpB-tgt u) (cnil (tgt-dim k c)))
  cp-tgt j k {node x r} le (cp u) | false = cp (tgtB j k (≤-≢→< le e) u)

  tgtB : ∀ j k {x r c} → k < j → CpB k x r c → CpB k x (bdpB j (suc k) r) (tgt j c)
  tgtB j k lt (cnil {x} d) = subst (CpB k x nil) (sym (dim-tgt-up (<→≤ lt) d)) (cnil d)
  tgtB j k {x} lt (ccons {T = T} {y} {r} {a} {b} ca e cb p) =
    subst (CpB k x (cons (bdp j (suc k) T) y (bdpB j (suc k) r))) (sym (tgt-comp-> a b p lt q))
      (ccons (cp-tgt j (suc k) lt ca) (trans (src-tgt-< a lt) e) (tgtB j k lt cb) q)
    where
    q : tgt k (tgt j a) ≡ src k (tgt j b)
    q = trans (tgt-tgt-< a lt) (trans p (sym (src-tgt-< b lt)))

------------------------------------------------------------------------
-- Gluing along height j.

mutual
  glue : Nat → Nat → LT → LT → LT
  glue j k (node x r₁) (node _ r₂) with j ==ℕ k
  ... | true  = node x (r₁ ++B r₂)
  ... | false = node x (glueB j (suc k) r₁ r₂)

  glueB : Nat → Nat → Br → Br → Br
  glueB j k nil            _                = nil
  glueB j k (cons T y r)   nil              = cons T y r
  glueB j k (cons T₁ y r₁) (cons T₂ _ r₂)   = cons (glue j k T₁ T₂) y (glueB j k r₁ r₂)

-- Gluing along the spine (j = k) is associativity.
cat : ∀ k {x y r₁ r₂ c₁ c₂} → CpB k x r₁ c₁ → CpB k y r₂ c₂ → lastv x r₁ ≡ y →
      ∀ p → CpB k x (r₁ ++B r₂) (comp k c₁ c₂ p)
cat k {x} {r₂ = r₂} {c₂ = c₂} (cnil d) v refl p =
  subst (CpB k x r₂) (sym eq) v
  where
  p″ : tgt k (src k c₂) ≡ src k c₂
  p″ = tgt-src-≥ c₂ (≤-refl k)
  eq : comp k x c₂ p ≡ c₂
  eq = trans (comp-cong k p p″ (sym (cpB-src v)) refl) (unit-l k c₂ p″)
cat k {x} {r₂ = r₂} {c₂ = c₂} (ccons {T = T} {y₁} {r₁} {a} {b} ca e cb p₁) v l p =
  subst (CpB k x (cons T y₁ (r₁ ++B r₂))) (sym (assoc k a b c₂ p₁ p p′ q))
    (ccons ca e (cat k cb v l p′) q)
  where
  p′ : tgt k b ≡ src k c₂
  p′ = trans (sym (tgt-comp k a b p₁)) p
  q : tgt k a ≡ src k (comp k b c₂ p′)
  q = trans p₁ (sym (src-comp k b c₂ p′))

private
  cons-T : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → T ≡ T′
  cons-T {T = T} e = cong (hdB T) e

  cons-y : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → y ≡ y′
  cons-y {y = y} e = cong (vB y) e

  cons-r : ∀ {T T′ y y′ r r′} → cons T y r ≡ cons T′ y′ r′ → r ≡ r′
  cons-r e = cong tlB e

  node-x : ∀ {x x′ r r′} → node x r ≡ node x′ r′ → x ≡ x′
  node-x e = cong rootLT e

  node-r : ∀ {x x′ r r′} → node x r ≡ node x′ r′ → r ≡ r′
  node-r e = cong kidsLT e

mutual
  -- Binary pasting lemma.
  cp-glue : ∀ j k {S₁ S₂ c₁ c₂} → k ≤ j → Cp k S₁ c₁ → Cp k S₂ c₂ → bdp j k S₁ ≡ bdm j k S₂ →
            ∀ p → Cp k (glue j k S₁ S₂) (comp j c₁ c₂ p)
  cp-glue j k {node x r₁} {node y r₂} le (cp u) (cp v) eb p with j ==ℕ k in e
  ... | true with ==→≡ j k e
  ...   | refl = cp (cat k u v (node-x eb) p)
  cp-glue j k {node x r₁} {node y r₂} le (cp u) (cp v) eb p | false
    with node-x eb
  ... | refl = cp (zipB j k (≤-≢→< le e) u v (node-r eb) p)

  zipB : ∀ j k {x r₁ r₂ c₁ c₂} → k < j → CpB k x r₁ c₁ → CpB k x r₂ c₂ →
         bdpB j (suc k) r₁ ≡ bdmB j (suc k) r₂ → ∀ p → CpB k x (glueB j (suc k) r₁ r₂) (comp j c₁ c₂ p)
  zipB j k {x} lt (cnil d) (cnil _) _ p = subst (CpB k x nil) (sym eq) (cnil d)
    where
    dj : src j x ≡ x
    dj = dim-up (<→≤ lt) d
    p″ : tgt j (src j x) ≡ src j x
    p″ = tgt-src-≥ x (≤-refl j)
    eq : comp j x x p ≡ x
    eq = trans (comp-cong j p p″ (sym dj) refl) (unit-l j x p″)
  zipB j k _ (cnil _) (ccons _ _ _ _) () p
  zipB j k _ (ccons _ _ _ _) (cnil _) () p
  zipB j k {x} lt (ccons {T = T₁} {y₁} {r₁} {a₁} {b₁} ca₁ e₁ cb₁ p₁)
                  (ccons {T = T₂} {y₂} {r₂} {a₂} {b₂} ca₂ e₂ cb₂ p₂) eb p
    with cons-y eb
  ... | refl =
    subst (CpB k x (cons (glue j (suc k) T₁ T₂) y₁ (glueB j (suc k) r₁ r₂)))
      (interchange a₁ a₂ b₁ b₂ lt pa pb q p₁ p₂ p)
      (ccons (cp-glue j (suc k) lt ca₁ ca₂ (cons-T eb) pa)
             (trans (src-comp-< a₁ a₂ pa lt) e₁)
             (zipB j k lt cb₁ cb₂ (cons-r eb) pb)
             q)
    where
    pa : tgt j a₁ ≡ src j a₂
    pa = cp-det (subst (λ S → Cp (suc k) S (tgt j a₁)) (cons-T eb) (cp-tgt j (suc k) lt ca₁))
                (cp-src j (suc k) lt ca₂)
    pb : tgt j b₁ ≡ src j b₂
    pb = cpB-det (subst (λ R → CpB k y₁ R (tgt j b₁)) (cons-r eb) (tgtB j k lt cb₁))
                 (srcB j k lt cb₂)
    q : tgt k (comp j a₁ a₂ pa) ≡ src k (comp j b₁ b₂ pb)
    q = trans (tgt-comp-< a₁ a₂ pa lt)
          (trans p₂ (trans (cpB-src cb₂) (trans (sym (cpB-src cb₁)) (sym (src-comp-< b₁ b₂ pb lt)))))

-- Composability of glued trees follows from the boundary condition.
glue-ok : ∀ j k {S₁ S₂ c₁ c₂} → k ≤ j → Cp k S₁ c₁ → Cp k S₂ c₂ → bdp j k S₁ ≡ bdm j k S₂ →
          tgt j c₁ ≡ src j c₂
glue-ok j k {c₁ = c₁} le d₁ d₂ eb =
  cp-det (subst (λ S → Cp k S (tgt j c₁)) eb (cp-tgt j k le d₁)) (cp-src j k le d₂)
