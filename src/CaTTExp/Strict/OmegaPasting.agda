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
--   * boundary lemma: for a tree at level k, s_{d+k} and t_{d+k} of its
--     composite are the composites of its truncations at relative height
--     d (`cp-src`, `cp-tgt`);
--   * binary pasting lemma: the composite of two trees glued along
--     their common boundary at relative height d is the #_{d+k}-composite
--     of their composites (`cp-glue`). The d = 0 case is associativity,
--     the d > 0 case is interchange of #ₖ with #_{d+k}, folded along the
--     spine.
------------------------------------------------------------------------
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.OmegaPasting (𝒞 : ωCat) where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Trees
open ωCat 𝒞
open Basics 𝒞

private
  +-suc : ∀ d k → d + suc k ≡ suc (d + k)
  +-suc zero    k = refl
  +-suc (suc d) k = cong suc (+-suc d k)

  ≤-+ : ∀ d k → k ≤ d + k
  ≤-+ zero    k = ≤-refl k
  ≤-+ (suc d) k = ≤-suc (≤-+ d k)

  <-+ : ∀ d k → k < suc d + k
  <-+ d k = s≤s (≤-+ d k)

-- Composition does not depend on how its index is written.
comp-idx : ∀ {j j′} → j ≡ j′ → ∀ x y (p : tgt j x ≡ src j y) (p′ : tgt j′ x ≡ src j′ y) →
           comp j x y p ≡ comp j′ x y p′
comp-idx refl x y p p′ = cong (comp _ x y) (uip p p′)

------------------------------------------------------------------------
-- Composites.

mutual
  data Cp (k : Nat) : LT C → C → Set where
    cp : ∀ {x r c} → CpB k x r c → Cp k (node x r) c

  -- CpB k x r c: the spine starting at x with branches r composes to c.
  data CpB (k : Nat) : C → Br C → C → Set where
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
-- Boundary lemma: truncating at relative height d takes the boundary at
-- d + k.

mutual
  cp-src : ∀ d k {T c} → Cp k T c → Cp k (bdm d T) (src (d + k) c)
  cp-src zero k {node x r} {c} (cp u) =
    cp (subst (λ z → CpB k z nil (src k c)) (cpB-src u) (cnil (src-dim k c)))
  cp-src (suc d) k {node x r} (cp u) = cp (srcB d k u)

  srcB : ∀ d k {x r c} → CpB k x r c → CpB k x (bdmB d r) (src (suc d + k) c)
  srcB d k (cnil {x} dx) = subst (CpB k x nil) (sym (dim-up (<→≤ (<-+ d k)) dx)) (cnil dx)
  srcB d k {x} (ccons {T = T} {y} {r} {a} {b} ca e cb p) =
    subst (CpB k x (cons (bdm d T) y (bdmB d r))) (sym (src-comp-> a b p lt q))
      (ccons (subst (λ j → Cp (suc k) (bdm d T) (src j a)) (+-suc d k) (cp-src d (suc k) ca))
             (trans (src-src-< a lt) e) (srcB d k cb) q)
    where
    lt = <-+ d k
    q : tgt k (src (suc d + k) a) ≡ src k (src (suc d + k) b)
    q = trans (tgt-src-< a lt) (trans p (sym (src-src-< b lt)))

mutual
  cp-tgt : ∀ d k {T c} → Cp k T c → Cp k (bdp d T) (tgt (d + k) c)
  cp-tgt zero k {node x r} {c} (cp u) =
    cp (subst (λ z → CpB k z nil (tgt k c)) (cpB-tgt u) (cnil (tgt-dim k c)))
  cp-tgt (suc d) k {node x r} (cp u) = cp (tgtB d k u)

  tgtB : ∀ d k {x r c} → CpB k x r c → CpB k x (bdpB d r) (tgt (suc d + k) c)
  tgtB d k (cnil {x} dx) = subst (CpB k x nil) (sym (dim-tgt-up (<→≤ (<-+ d k)) dx)) (cnil dx)
  tgtB d k {x} (ccons {T = T} {y} {r} {a} {b} ca e cb p) =
    subst (CpB k x (cons (bdp d T) y (bdpB d r))) (sym (tgt-comp-> a b p lt q))
      (ccons (subst (λ j → Cp (suc k) (bdp d T) (tgt j a)) (+-suc d k) (cp-tgt d (suc k) ca))
             (trans (src-tgt-< a lt) e) (tgtB d k cb) q)
    where
    lt = <-+ d k
    q : tgt k (tgt (suc d + k) a) ≡ src k (tgt (suc d + k) b)
    q = trans (tgt-tgt-< a lt) (trans p (sym (src-tgt-< b lt)))

------------------------------------------------------------------------
-- Gluing.

-- Gluing along the spine (d = 0) is associativity.
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

mutual
  -- Binary pasting lemma.
  cp-glue : ∀ d k {S₁ S₂ c₁ c₂} → Cp k S₁ c₁ → Cp k S₂ c₂ → bdp d S₁ ≡ bdm d S₂ →
            ∀ p → Cp k (glue d S₁ S₂) (comp (d + k) c₁ c₂ p)
  cp-glue zero    k {node x r₁} {node y r₂} (cp u) (cp v) eb p = cp (cat k u v (node-x eb) p)
  cp-glue (suc d) k {node x r₁} {node y r₂} (cp u) (cp v) eb p with node-x eb
  ... | refl = cp (zipB d k u v (node-r eb) p)

  zipB : ∀ d k {x r₁ r₂ c₁ c₂} → CpB k x r₁ c₁ → CpB k x r₂ c₂ →
         bdpB d r₁ ≡ bdmB d r₂ → ∀ p → CpB k x (glueB d r₁ r₂) (comp (suc d + k) c₁ c₂ p)
  zipB d k {x} (cnil dx) (cnil _) _ p = subst (CpB k x nil) (sym eq) (cnil dx)
    where
    j = suc d + k
    dj : src j x ≡ x
    dj = dim-up (<→≤ (<-+ d k)) dx
    p″ : tgt j (src j x) ≡ src j x
    p″ = tgt-src-≥ x (≤-refl j)
    eq : comp j x x p ≡ x
    eq = trans (comp-cong j p p″ (sym dj) refl) (unit-l j x p″)
  zipB d k (cnil _) (ccons _ _ _ _) () p
  zipB d k (ccons _ _ _ _) (cnil _) () p
  zipB d k {x} (ccons {T = T₁} {y₁} {r₁} {a₁} {b₁} ca₁ e₁ cb₁ p₁)
               (ccons {T = T₂} {y₂} {r₂} {a₂} {b₂} ca₂ e₂ cb₂ p₂) eb p
    with cons-y eb
  ... | refl =
    subst (CpB k x (cons (glue d T₁ T₂) y₁ (glueB d r₁ r₂)))
      (interchange a₁ a₂ b₁ b₂ lt pa pb q p₁ p₂ p)
      (ccons (subst (Cp (suc k) (glue d T₁ T₂)) (comp-idx (+-suc d k) a₁ a₂ pa₀ pa)
                    (cp-glue d (suc k) ca₁ ca₂ (cons-T eb) pa₀))
             (trans (src-comp-< a₁ a₂ pa lt) e₁)
             (zipB d k cb₁ cb₂ (cons-r eb) pb)
             q)
    where
    j  = suc d + k
    lt = <-+ d k
    pa₀ : tgt (d + suc k) a₁ ≡ src (d + suc k) a₂
    pa₀ = cp-det (subst (λ S → Cp (suc k) S (tgt (d + suc k) a₁)) (cons-T eb) (cp-tgt d (suc k) ca₁))
                 (cp-src d (suc k) ca₂)
    pa : tgt j a₁ ≡ src j a₂
    pa = subst (λ i → tgt i a₁ ≡ src i a₂) (+-suc d k) pa₀
    pb : tgt j b₁ ≡ src j b₂
    pb = cpB-det (subst (λ R → CpB k y₁ R (tgt j b₁)) (cons-r eb) (tgtB d k cb₁))
                 (srcB d k cb₂)
    q : tgt k (comp j a₁ a₂ pa) ≡ src k (comp j b₁ b₂ pb)
    q = trans (tgt-comp-< a₁ a₂ pa lt)
          (trans p₂ (trans (cpB-src cb₂) (trans (sym (cpB-src cb₁)) (sym (src-comp-< b₁ b₂ pb lt)))))

-- Composability of glued trees follows from the boundary condition.
glue-ok : ∀ d k {S₁ S₂ c₁ c₂} → Cp k S₁ c₁ → Cp k S₂ c₂ → bdp d S₁ ≡ bdm d S₂ →
          tgt (d + k) c₁ ≡ src (d + k) c₂
glue-ok d k {c₁ = c₁} d₁ d₂ eb =
  cp-det (subst (λ S → Cp k S (tgt (d + k) c₁)) eb (cp-tgt d k d₁)) (cp-src d k d₂)
