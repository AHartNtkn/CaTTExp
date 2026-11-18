------------------------------------------------------------------------
-- Augmented directed complexes with a finite basis (ledger A5, N0).
--
-- A basis b₀, …, b_{N−1} with degrees gᵢ and boundary parts ∂^±bᵢ
-- (non-negative chains) gives an `ADC` (CaTTExp.Strict.Nu): chains are
-- vectors of N natural numbers, ∂^± is extended linearly, πⱼ keeps the
-- coefficients of degree-j elements, and ε counts the degree-0 ones.
-- This is Steiner's K* for a complex with a finite basis; `ν` below is
-- ν(K) as a strict ω-category, cells of dimension < L.
------------------------------------------------------------------------
module CaTTExp.Strict.FreeADC where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (ωCat)
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero)

record Basis (N : Nat) : Set where
  field
    gdeg   : Vec Nat N
    bplus  : Vec (Vec Nat N) N
    bminus : Vec (Vec Nat N) N

Chn : Nat → Set
Chn N = Vec Nat N

0c : ∀ {m} → Vec Nat m
0c {zero}  = []
0c {suc m} = 0 ∷ 0c

_+c_ : ∀ {m} → Vec Nat m → Vec Nat m → Vec Nat m
[]      +c []        = []
(a ∷ u) +c (b ∷ v)   = (a + b) ∷ (u +c v)

+c-id : ∀ {m} (u : Vec Nat m) → 0c +c u ≡ u
+c-id []      = refl
+c-id (a ∷ u) = cong (a ∷_) (+c-id u)

+c-comm : ∀ {m} (u v : Vec Nat m) → u +c v ≡ v +c u
+c-comm []      []      = refl
+c-comm (a ∷ u) (b ∷ v) = cong₂ _∷_ (+-comm a b) (+c-comm u v)

+c-assoc : ∀ {m} (u v w : Vec Nat m) → (u +c v) +c w ≡ u +c (v +c w)
+c-assoc []      []      []      = refl
+c-assoc (a ∷ u) (b ∷ v) (c ∷ w) = cong₂ _∷_ (+-assoc a b c) (+c-assoc u v w)

private
  +-cancel : ∀ a b c → a + c ≡ b + c → a ≡ b
  +-cancel a b zero    p = trans (sym (+-zero a)) (trans p (+-zero b))
  +-cancel a b (suc c) p = +-cancel a b c (suc-inj (trans (sym (+-suc′ a c)) (trans p (+-suc′ b c))))
    where
    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
    +-suc′ : ∀ m n → m + suc n ≡ suc (m + n)
    +-suc′ zero    n = refl
    +-suc′ (suc m) n = cong suc (+-suc′ m n)

  ∷-inj : ∀ {m} {a b : Nat} {u v : Vec Nat m} → a ∷ u ≡ b ∷ v → (a ≡ b) × (u ≡ v)
  ∷-inj refl = refl , refl

  mid : ∀ {m} (a b c d : Vec Nat m) → (a +c b) +c (c +c d) ≡ (a +c c) +c (b +c d)
  mid a b c d =
    trans (+c-assoc a b (c +c d))
      (trans (cong (a +c_) (trans (sym (+c-assoc b c d)) (trans (cong (_+c d) (+c-comm b c)) (+c-assoc c b d))))
             (sym (+c-assoc a c (b +c d))))

+c-cancel : ∀ {m} (u v w : Vec Nat m) → u +c w ≡ v +c w → u ≡ v
+c-cancel []      []      []      p = refl
+c-cancel (a ∷ u) (b ∷ v) (c ∷ w) p =
  let (h , t) = ∷-inj p in cong₂ _∷_ (+-cancel a b c h) (+c-cancel u v w t)

-- Scalar multiples by repeated addition.
_⊙_ : ∀ {m} → Nat → Vec Nat m → Vec Nat m
zero  ⊙ v = 0c
suc k ⊙ v = v +c (k ⊙ v)

⊙-+ : ∀ {m} a b (v : Vec Nat m) → (a + b) ⊙ v ≡ (a ⊙ v) +c (b ⊙ v)
⊙-+ zero    b v = sym (+c-id (b ⊙ v))
⊙-+ (suc a) b v = trans (cong (v +c_) (⊙-+ a b v)) (sym (+c-assoc v (a ⊙ v) (b ⊙ v)))

-- Linear extension.
lin : ∀ {N m} → Vec Nat m → Vec (Vec Nat N) m → Vec Nat N
lin []      []        = 0c
lin (k ∷ c) (v ∷ vs)  = (k ⊙ v) +c lin c vs

lin-0 : ∀ {N m} (vs : Vec (Vec Nat N) m) → lin 0c vs ≡ 0c
lin-0 []       = refl
lin-0 (v ∷ vs) = trans (+c-id (lin 0c vs)) (lin-0 vs)

lin-+ : ∀ {N m} (c d : Vec Nat m) (vs : Vec (Vec Nat N) m) → lin (c +c d) vs ≡ lin c vs +c lin d vs
lin-+ []      []      []       = sym (+c-id 0c)
lin-+ (a ∷ c) (b ∷ d) (v ∷ vs) =
  trans (cong₂ _+c_ (⊙-+ a b v) (lin-+ c d vs)) (mid (a ⊙ v) (b ⊙ v) (lin c vs) (lin d vs))

-- Degree projection and augmentation.
prj : ∀ {m} → Nat → Vec Nat m → Vec Nat m → Vec Nat m
prj j []       []      = []
prj j (g ∷ gs) (k ∷ c) = (if g ==ℕ j then k else 0) ∷ prj j gs c

prj-0 : ∀ {m} j (gs : Vec Nat m) → prj j gs 0c ≡ 0c
prj-0 j []       = refl
prj-0 j (g ∷ gs) with g ==ℕ j
... | true  = cong (0 ∷_) (prj-0 j gs)
... | false = cong (0 ∷_) (prj-0 j gs)

prj-+ : ∀ {m} j (gs : Vec Nat m) c d → prj j gs (c +c d) ≡ prj j gs c +c prj j gs d
prj-+ j []       []      []      = refl
prj-+ j (g ∷ gs) (a ∷ c) (b ∷ d) with g ==ℕ j
... | true  = cong ((a + b) ∷_) (prj-+ j gs c d)
... | false = cong (0 ∷_) (prj-+ j gs c d)

augm : ∀ {m} → Vec Nat m → Vec Nat m → Nat
augm []       []      = 0
augm (g ∷ gs) (k ∷ c) = (if g ==ℕ 0 then k else 0) + augm gs c

chainMon : Nat → CMon
chainMon N = record
  { M = Chn N ; ε = 0c ; _⊕_ = _+c_
  ; ⊕-id = +c-id ; ⊕-comm = +c-comm ; ⊕-assoc = +c-assoc }

adc : ∀ {N} → Basis N → ADC
adc B = record
  { 𝕄 = chainMon _
  ; cancel = +c-cancel
  ; ∂⁺ = λ c → lin c bplus
  ; ∂⁻ = λ c → lin c bminus
  ; ∂⁺-ε = lin-0 bplus
  ; ∂⁻-ε = lin-0 bminus
  ; ∂⁺-⊕ = λ a b → lin-+ a b bplus
  ; ∂⁻-⊕ = λ a b → lin-+ a b bminus
  ; π = λ j → prj j gdeg
  ; π-ε = λ j → prj-0 j gdeg
  ; π-⊕ = λ j → prj-+ j gdeg
  ; aug = augm gdeg
  }
  where open Basis B

-- ν(K), cells of dimension < L.
ν : ∀ {N} → Basis N → Nat → ωCat
ν B L = nu (adc B) L

------------------------------------------------------------------------
-- Example: the arrow D¹ (x₀, y₁, f₂ : x → y). Its atom ⟨f⟩ is a 1-cell
-- of ν(λD¹) from ⟨x⟩ to ⟨y⟩, and the cell conditions hold by evaluation.

private
  z3 : Vec Nat 3
  z3 = 0c {3}

  e0 e1 e2 : Vec Nat 3
  e0 = 1 ∷ 0 ∷ 0 ∷ []
  e1 = 0 ∷ 1 ∷ 0 ∷ []
  e2 = 0 ∷ 0 ∷ 1 ∷ []

  BD¹ : Basis 3
  BD¹ = record { gdeg = 0 ∷ 0 ∷ 1 ∷ []
               ; bplus  = z3 ∷ z3 ∷ e1 ∷ []
               ; bminus = z3 ∷ z3 ∷ e0 ∷ [] }

  atom-f : ωCat.C (ν BD¹ 1)
  atom-f = ((e0 , e1) ∷ (e2 , e2) ∷ []) ,
           ((refl , refl , refl , refl) , ((refl , refl , refl , refl) , tt) , refl)

  _ : ωCat.src (ν BD¹ 1) 0 atom-f ≡
      (((e0 , e0) ∷ (z3 , z3) ∷ []) , ((refl , refl , refl , refl) , ((refl , refl , refl , refl) , tt) , refl))
  _ = refl
