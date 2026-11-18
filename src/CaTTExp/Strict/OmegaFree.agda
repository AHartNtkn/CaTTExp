------------------------------------------------------------------------
-- From the free model to any strict ω-category (ledger item A3a,
-- general case).
--
-- Fix a labelling λ of variables by cells of 𝒞. A tree X of variables
-- is sent to the composite of X relabelled by λ, when it exists:
--
--     Φ X c  ⇔  Cp 0 (mapLT λ X) c.
--
-- By the boundary and binary pasting lemmas (CaTTExp.Strict.
-- OmegaPasting) Φ is functional and preserves sources, targets and
-- composites, so the functor lemma (CaTTExp.Strict.OmegaFunctor)
-- applies to it. If λ gives each variable of a pasting context Θ a
-- cell with the boundary its type prescribes (`Good`), the generic
-- environment η Θ is Φ-related to λ (`η-R`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.OmegaFree
  (𝕊 : Signature) (𝒞 : ωCat) (Mk : Signature.K 𝕊 → ωCat.C 𝒞 → Set)
  (λ′ : Nat → ωCat.C 𝒞)
  where

open Signature 𝕊
open ωCat 𝒞
open Basics 𝒞
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.OmegaPasting 𝒞
open import CaTTExp.Strict.GenericEnv 𝕊
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd; PsCtx; ==→≡; lookup-<)
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ)
import CaTTExp.Strict.OmegaEval 𝕊 𝒯 M𝒯 as E𝒯
import CaTTExp.Strict.OmegaEval 𝕊 𝒞 Mk as E

Φ : LT Nat → C → Set
Φ X c = Cp 0 (mapLT λ′ X) c

private
  sub-cp : ∀ {T T′ c} → T ≡ T′ → Cp 0 T c → Cp 0 T′ c
  sub-cp refl d = d

  sub-val : ∀ {T c c′} → c ≡ c′ → Cp 0 T c → Cp 0 T c′
  sub-val refl d = d

Φ-src : ∀ n {X c} → Φ X c → Φ (bdm n X) (src n c)
Φ-src n {X} d = sub-cp (sym (map-bdm λ′ n X)) (sub-val (cong (λ m → src m _) (+-zero n)) (cp-src n 0 d))

Φ-tgt : ∀ n {X c} → Φ X c → Φ (bdp n X) (tgt n c)
Φ-tgt n {X} d = sub-cp (sym (map-bdp λ′ n X)) (sub-val (cong (λ m → tgt m _) (+-zero n)) (cp-tgt n 0 d))

Φ-det : ∀ {X c c′} → Φ X c → Φ X c′ → c ≡ c′
Φ-det = cp-det

Φ-comp : ∀ n {X c X′ c′} → Φ X c → Φ X′ c′ → ∀ (p : bdp n X ≡ bdm n X′) q →
         Φ (glue n X X′) (comp n c c′ q)
Φ-comp n {X} {c} {X′} {c′} d d′ p q =
  sub-cp (sym (map-glue λ′ n X X′))
    (sub-val (comp-idx (+-zero n) c c′ p″ q) (cp-glue n 0 d d′ p′ p″))
  where
  p′ : bdp n (mapLT λ′ X) ≡ bdm n (mapLT λ′ X′)
  p′ = trans (sym (map-bdp λ′ n X)) (trans (cong (mapLT λ′) p) (map-bdm λ′ n X′))
  p″ : tgt (n + 0) c ≡ src (n + 0) c′
  p″ = glue-ok n 0 d d′ p′

open import CaTTExp.Strict.OmegaFunctor 𝕊 𝒯 𝒞 M𝒯 Mk Φ Φ-src Φ-tgt Φ-det Φ-comp (λ ()) public

------------------------------------------------------------------------
-- Discs.

BdL : C → Ty → Set
BdL c ⋆           = ⊤
BdL c (arr B s u) = (src (dim B) c ≡ λ′ (vn s)) × (tgt (dim B) c ≡ λ′ (vn u))

-- λ gives each variable of Γ a cell with the boundary its type
-- prescribes.
Good : Ctx → Set
Good Γ = ∀ v A → lookup Γ v ≡ just A → Dim≤ (dim A) (λ′ v) × BdL (λ′ v) A

-- All iterated boundaries of c match those prescribed by B.
Matches : C → Ty → Set
Matches c ⋆           = ⊤
Matches c (arr B s u) = BdL c (arr B s u) × Matches c B

private
  ==-r : ∀ n → (n ==ℕ n) ≡ true
  ==-r zero    = refl
  ==-r (suc n) = ==-r n

  n<s : ∀ n → T (n <ℕ suc n)
  n<s zero    = tt
  n<s (suc n) = n<s n

  <s : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <s zero    (suc n) _ = tt
  <s (suc i) (suc n) q = <s i n q

  ≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  ≢ zero    (suc n) _ = refl
  ≢ (suc i) (suc n) q = ≢ i n q

  ≤-step : ∀ {m n} → m < n → m < suc n
  ≤-step {m} p = ≤-trans p (≤-suc (≤-refl _))

matches-transfer : ∀ B x y → (∀ j → j < dim B → (src j y ≡ src j x) × (tgt j y ≡ tgt j x)) →
                   Matches x B → Matches y B
matches-transfer ⋆           x y h m = tt
matches-transfer (arr B s u) x y h ((ms , mt) , m) =
  let (es , et) = h (dim B) (≤-refl _) in
  (trans es ms , trans et mt) ,
  matches-transfer B x y (λ j l → h j (≤-step l)) m

module _ {Θ : Ctx} (ord : ArrOrd Θ) (sh : PsCtx Θ) (good : Good Θ) where

  matches : ∀ A v → lookup Θ v ≡ just A → Matches (λ′ v) A
  matches A v p = go A (sh v A p) v p
    where
    go : ∀ A → PsTy A → ∀ v → lookup Θ v ≡ just A → Matches (λ′ v) A
    go ⋆ ⋆ₚ v p = tt
    go (arr B (var a) (var b)) (arrₚ pB) v p =
      let (la , _ , _) = ord v B a b p
          bd = snd (good v _ p)
          ma = go B pB a la
      in bd ,
         matches-transfer B (λ′ a) (λ′ v)
           (λ j l → trans (sym (src-src-< (λ′ v) l)) (cong (src j) (fst bd)) ,
                    trans (sym (tgt-src-< (λ′ v) l)) (cong (tgt j) (fst bd)))
           ma

  cp-discT : ∀ B T c → Cp (dim B) (mapLT λ′ T) c → Matches c B → Cp 0 (mapLT λ′ (discT B T)) c
  cp-discT ⋆           T c d m = d
  cp-discT (arr B s u) T c d ((ms , mt) , m) =
    cp-discT B (node (vn s) (cons T (vn u) nil)) c
      (sub-val′ (trans (comp-cong k p p₀ refl (sym mt)) (unit-r k c p₀))
        (cp (ccons d ms (cnil dimu) p)))
      m
    where
    k = dim B
    sub-val′ : ∀ {T c c′} → c ≡ c′ → Cp k T c → Cp k T c′
    sub-val′ refl x = x
    dimu : Dim≤ k (λ′ (vn u))
    dimu = subst (Dim≤ k) mt (tgt-dim k c)
    p : tgt k c ≡ src k (λ′ (vn u))
    p = trans mt (sym dimu)
    p₀ : tgt k c ≡ src k (tgt k c)
    p₀ = sym (tgt-dim k c)

  Φ-disc : ∀ v A → lookup Θ v ≡ just A → Φ (disc v A) (λ′ v)
  Φ-disc v A p = cp-discT A (node v nil) (λ′ v) (cp (cnil (fst (good v A p)))) (matches A v p)

  -- The generic environment is related to λ, given an environment
  -- that agrees with λ on Θ.
  η-R : ∀ {Γ} (ρ : E.Env) → E.lenₑ ρ ≡ len Γ → (∀ v A → lookup Γ v ≡ just A → lookup Θ v ≡ just A) →
        (∀ v → T (v <ℕ len Γ) → E.lkd ρ (λ′ 0) v ≡ λ′ v) → EnvR (η Γ) ρ
  η-R {ε}     E.[]ₑ      l pre agree = []ᵣ
  η-R {Γ ▸ A} (ρ E.,ₑ c) l pre agree =
    η-R {Γ} ρ (suc-inj l) (λ v B q → pre v B (wk v B q))
      (λ v lt → trans (sym (lkd-skip v lt)) (agree v (<s v (len Γ) lt))) ,ᵣ
    subst (Φ (disc (len Γ) A)) (sym top) (Φ-disc (len Γ) A (pre (len Γ) A (top-l Γ A)))
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
    top-l : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
    top-l Γ A rewrite ==-r (len Γ) = refl
    wk : ∀ v B → lookup Γ v ≡ just B → lookup (Γ ▸ A) v ≡ just B
    wk v B q rewrite ≢ v (len Γ) (lookup-< Γ v q) = q
    lkd-skip : ∀ v → T (v <ℕ len Γ) → E.lkd (ρ E.,ₑ c) (λ′ 0) v ≡ E.lkd ρ (λ′ 0) v
    lkd-skip v lt rewrite suc-inj l | ≢ v (len Γ) lt = refl
    top : c ≡ λ′ (len Γ)
    top = trans (sym (lkd-top)) (agree (len Γ) (n<s (len Γ)))
      where
      lkd-top : E.lkd (ρ E.,ₑ c) (λ′ 0) (len Γ) ≡ c
      lkd-top rewrite suc-inj l | ==-r (len Γ) = refl
