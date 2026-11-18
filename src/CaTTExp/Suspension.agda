------------------------------------------------------------------------
-- Suspension is admissible (ledger item C8.1).
--
-- Σ adds two new objects N (level 0) and S (level 1) in front of a
-- context and shifts every type up one dimension: ⋆ becomes N → S.
-- Every coherence over Θ becomes a coherence over ΣΘ.
--
--   Γ ⊢ctx        implies  ΣΓ ⊢ctx
--   Γ ⊢ty A       implies  ΣΓ ⊢ty ΣA
--   Γ ⊢tm t ∶ A   implies  ΣΓ ⊢tm Σt ∶ ΣA
--   Γ ⊢sub σ ∶ Δ  implies  ΣΓ ⊢sub Σσ ∶ ΣΔ
--
-- This is what makes the elements elaboration of
-- `limits-representables.md` §5.1 / R-C well typed: a CaTT derivation
-- in a context "fibred over C" (x y : C, f : x →_C y, …) is a
-- derivation in Γ, its translation is Σt in ΣΓ, and any ambient
-- substitution N ↦ ⊤, S ↦ C, … then lands it in the ambient by
-- substitution admissibility (`elements` below).
--
-- Hypothesis: the syntax is constant free (`FNc…`), coh bodies
-- included, since a constant's type is not suspended. Pure CaTT is
-- constant free, so for pure CaTT there is no hypothesis.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Suspension (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
import CaTTExp.Subst 𝕊 cattSide as Sb

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

S : Nat → Nat
S n = suc (suc n)

------------------------------------------------------------------------
-- The operation.

mutual
  Σty : Ty → Ty
  Σty ⋆           = arr ⋆ (var 0) (var 1)
  Σty (arr A t u) = arr (Σty A) (Σtm t) (Σtm u)

  Σtm : Tm → Tm
  Σtm (var i)     = var (S i)
  Σtm (coh Θ A τ) = coh (Σctx Θ) (Σty A) (Σsub τ)
  Σtm (cst k)     = cst k

  Σsub : Sub → Sub
  Σsub ⟨⟩       = ⟨⟩ ,ₛ var 0 ,ₛ var 1
  Σsub (τ ,ₛ t) = Σsub τ ,ₛ Σtm t

  Σctx : Ctx → Ctx
  Σctx ε       = ε ▸ ⋆ ▸ ⋆
  Σctx (Γ ▸ A) = Σctx Γ ▸ Σty A

-- Constant-free syntax, coh bodies included.
mutual
  FNcTy : Ty → Set
  FNcTy ⋆           = ⊤
  FNcTy (arr A t u) = FNcTy A × FNcTm t × FNcTm u

  FNcTm : Tm → Set
  FNcTm (var _)     = ⊤
  FNcTm (coh Θ A τ) = FNcCtx Θ × FNcTy A × FNcSub τ
  FNcTm (cst _)     = ⊥

  FNcSub : Sub → Set
  FNcSub ⟨⟩       = ⊤
  FNcSub (σ ,ₛ t) = FNcSub σ × FNcTm t

  FNcCtx : Ctx → Set
  FNcCtx ε       = ⊤
  FNcCtx (Γ ▸ A) = FNcCtx Γ × FNcTy A

------------------------------------------------------------------------
-- Arithmetic and lists.

private
  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

  ≡→T : ∀ {b} → b ≡ true → T b
  ≡→T refl = tt

  <-suc : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
  <-suc zero    (suc n) _ = tt
  <-suc (suc i) (suc n) p = <-suc i n p

  <→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  <→≢ zero    (suc n) _ = refl
  <→≢ (suc i) (suc n) p = <→≢ i n p

  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl n = T→≡ (==ℕ-refl n)

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  max-0 : ∀ n → max n 0 ≡ n
  max-0 zero    = refl
  max-0 (suc n) = refl

mapS : List Nat → List Nat
mapS []       = []
mapS (x ∷ xs) = S x ∷ mapS xs

-- The suspension of a variable set: N, S and the shifted variables.
Lift : List Nat → List Nat
Lift xs = 0 ∷ 1 ∷ mapS xs

private
  mapS-++ : ∀ xs ys → mapS (xs ++ ys) ≡ mapS xs ++ mapS ys
  mapS-++ []       ys = refl
  mapS-++ (x ∷ xs) ys = cong (S x ∷_) (mapS-++ xs ys)

  mapS-dropLast : ∀ xs → mapS (dropLast xs) ≡ dropLast (mapS xs)
  mapS-dropLast []           = refl
  mapS-dropLast (x ∷ [])     = refl
  mapS-dropLast (x ∷ y ∷ xs) = cong (S x ∷_) (mapS-dropLast (y ∷ xs))

------------------------------------------------------------------------
-- Membership.

Mem : Nat → List Nat → Set
Mem n xs = T (elem n xs)

private
  mem++ : ∀ n xs ys → Mem n (xs ++ ys) → Mem n xs ⊎ Mem n ys
  mem++ n []       ys p = inj₂ p
  mem++ n (x ∷ xs) ys p with n ==ℕ x
  ... | true  = inj₁ tt
  ... | false = mem++ n xs ys p

  mem++l : ∀ n xs ys → Mem n xs → Mem n (xs ++ ys)
  mem++l n (x ∷ xs) ys p with n ==ℕ x
  ... | true  = tt
  ... | false = mem++l n xs ys p

  mem++r : ∀ n xs ys → Mem n ys → Mem n (xs ++ ys)
  mem++r n []       ys p = p
  mem++r n (x ∷ xs) ys p with n ==ℕ x
  ... | true  = tt
  ... | false = mem++r n xs ys p

  mem-single : ∀ n x → Mem n (x ∷ []) → n ≡ x
  mem-single n x p with n ==ℕ x in e
  ... | true = ==ℕ-sound n x (≡→T e)

  mem-here : ∀ n xs → Mem n (n ∷ xs)
  mem-here n xs rewrite ==-refl n = tt

  mem-there : ∀ n x xs → Mem n xs → Mem n (x ∷ xs)
  mem-there n x xs p with n ==ℕ x
  ... | true  = tt
  ... | false = p

  mem-cons : ∀ n x xs → Mem n (x ∷ xs) → (n ≡ x) ⊎ Mem n xs
  mem-cons n x xs p with n ==ℕ x in e
  ... | true  = inj₁ (==ℕ-sound n x (≡→T e))
  ... | false = inj₂ p

  mem-mapS : ∀ m xs → Mem (S m) (mapS xs) → Mem m xs
  mem-mapS m (x ∷ xs) p with m ==ℕ x
  ... | true  = tt
  ... | false = mem-mapS m xs p

  mapS-mem : ∀ m xs → Mem m xs → Mem (S m) (mapS xs)
  mapS-mem m (x ∷ xs) p with m ==ℕ x
  ... | true  = tt
  ... | false = mapS-mem m xs p

  mapS-low : ∀ n xs → Mem n (mapS xs) → Σ Nat λ m → (n ≡ S m) × Mem m xs
  mapS-low n (x ∷ xs) p with mem-cons n (S x) (mapS xs) p
  ... | inj₁ refl = x , refl , mem-here x xs
  ... | inj₂ q    = let (m , e , r) = mapS-low n xs q in m , e , mem-there m x xs r

  ⊆?-sound : ∀ xs ys → T (⊆? xs ys) → ∀ n → Mem n xs → Mem n ys
  ⊆?-sound (x ∷ xs) ys p n q with mem-cons n x xs q
  ... | inj₁ refl = ∧-fst p
  ... | inj₂ r    = ⊆?-sound xs ys (∧-snd {elem x ys} p) n r

  ⊆?-complete : ∀ xs ys → (∀ n → Mem n xs → Mem n ys) → T (⊆? xs ys)
  ⊆?-complete []       ys h = tt
  ⊆?-complete (x ∷ xs) ys h =
    and (h x (mem-here x xs)) (⊆?-complete xs ys (λ n q → h n (mem-there n x xs q)))
    where
    and : ∀ {a b} → T a → T b → T (a ∧ b)
    and {true} _ q = q

-- "n is a member of Lift xs", as a proposition.
LMem : Nat → List Nat → Set
LMem n xs = (n ≡ 0) ⊎ (n ≡ 1) ⊎ (Σ Nat λ m → (n ≡ S m) × Mem m xs)

private
  Lift→ : ∀ n xs → Mem n (Lift xs) → LMem n xs
  Lift→ n xs p with mem-cons n 0 (1 ∷ mapS xs) p
  ... | inj₁ e = inj₁ e
  ... | inj₂ q with mem-cons n 1 (mapS xs) q
  ...   | inj₁ e = inj₂ (inj₁ e)
  ...   | inj₂ r = inj₂ (inj₂ (mapS-low n xs r))

  Lift← : ∀ n xs → LMem n xs → Mem n (Lift xs)
  Lift← .0 xs (inj₁ refl) = tt
  Lift← .1 xs (inj₂ (inj₁ refl)) = tt
  Lift← .(S m) xs (inj₂ (inj₂ (m , refl , p))) = mapS-mem m xs p

  LMem-map : ∀ {n} xs ys → (∀ m → Mem m xs → Mem m ys) → LMem n xs → LMem n ys
  LMem-map xs ys h (inj₁ e)                 = inj₁ e
  LMem-map xs ys h (inj₂ (inj₁ e))          = inj₂ (inj₁ e)
  LMem-map xs ys h (inj₂ (inj₂ (m , e , p))) = inj₂ (inj₂ (m , e , h m p))

-- Set equality, decided by ≈?.
SetEq : List Nat → List Nat → Set
SetEq xs ys = (∀ n → Mem n xs → Mem n ys) × (∀ n → Mem n ys → Mem n xs)

private
  ≈?-sound : ∀ xs ys → T (≈? xs ys) → SetEq xs ys
  ≈?-sound xs ys p = ⊆?-sound xs ys (∧-fst p) , ⊆?-sound ys xs (∧-snd {⊆? xs ys} p)

  ≈?-complete : ∀ xs ys → SetEq xs ys → T (≈? xs ys)
  ≈?-complete xs ys (f , g) = and (⊆?-complete xs ys f) (⊆?-complete ys xs g)
    where
    and : ∀ {a b} → T a → T b → T (a ∧ b)
    and {true} _ q = q

-- If Xs has the members of Lift X and F the members of Lift F′, then
-- F′ ≈ X gives ΣF ≈ Xs.
lift-≈ : ∀ F′ X ΣF Xs → T (≈? F′ X) →
         (∀ n → Mem n ΣF → LMem n F′) → (∀ n → LMem n F′ → Mem n ΣF) →
         (∀ n → Mem n Xs → LMem n X) → (∀ n → LMem n X → Mem n Xs) →
         T (≈? ΣF Xs)
lift-≈ F′ X ΣF Xs p f→ f← x→ x← =
  let (to , from) = ≈?-sound F′ X p in
  ≈?-complete ΣF Xs ((λ n q → x← n (LMem-map F′ X to (f→ n q))) ,
                     (λ n q → f← n (LMem-map X F′ from (x→ n q))))

------------------------------------------------------------------------
-- Free variables of suspended syntax.

mutual
  fvΣty→ : ∀ A n → Mem n (fvTy (Σty A)) → LMem n (fvTy A)
  fvΣty→ ⋆ n p with mem-cons n 0 (1 ∷ []) p
  ... | inj₁ e = inj₁ e
  ... | inj₂ q = inj₂ (inj₁ (mem-single n 1 q))
  fvΣty→ (arr A t u) n p with mem++ n (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) p
  ... | inj₁ q = LMem-map (fvTy A) FA (λ m r → mem++l m (fvTy A) (fvTm t ++ fvTm u) r) (fvΣty→ A n q)
    where FA = fvTy (arr A t u)
  ... | inj₂ q with mem++ n (fvTm (Σtm t)) (fvTm (Σtm u)) q
  ...   | inj₁ r = LMem-map (fvTm t) (fvTy (arr A t u))
                     (λ m r′ → mem++r m (fvTy A) (fvTm t ++ fvTm u) (mem++l m (fvTm t) (fvTm u) r′))
                     (fvΣtm→ t n r)
  ...   | inj₂ r = LMem-map (fvTm u) (fvTy (arr A t u))
                     (λ m r′ → mem++r m (fvTy A) (fvTm t ++ fvTm u) (mem++r m (fvTm t) (fvTm u) r′))
                     (fvΣtm→ u n r)

  fvΣtm→ : ∀ t n → Mem n (fvTm (Σtm t)) → LMem n (fvTm t)
  fvΣtm→ (var i)     n p = inj₂ (inj₂ (i , mem-single n (S i) p , mem-here i []))
  fvΣtm→ (coh Θ A τ) n p = fvΣsub→ τ n p
  fvΣtm→ (cst k)     n ()

  fvΣsub→ : ∀ σ n → Mem n (fvSub (Σsub σ)) → LMem n (fvSub σ)
  fvΣsub→ ⟨⟩ n p with mem-cons n 0 (1 ∷ []) p
  ... | inj₁ e = inj₁ e
  ... | inj₂ q = inj₂ (inj₁ (mem-single n 1 q))
  fvΣsub→ (σ ,ₛ t) n p with mem++ n (fvSub (Σsub σ)) (fvTm (Σtm t)) p
  ... | inj₁ q = LMem-map (fvSub σ) (fvSub (σ ,ₛ t)) (λ m r → mem++l m (fvSub σ) (fvTm t) r) (fvΣsub→ σ n q)
  ... | inj₂ q = LMem-map (fvTm t) (fvSub (σ ,ₛ t)) (λ m r → mem++r m (fvSub σ) (fvTm t) r) (fvΣtm→ t n q)

mutual
  fvΣty-low : ∀ A n → (n ≡ 0) ⊎ (n ≡ 1) → Mem n (fvTy (Σty A))
  fvΣty-low ⋆ .0 (inj₁ refl) = tt
  fvΣty-low ⋆ .1 (inj₂ refl) = tt
  fvΣty-low (arr A t u) n e = mem++l n (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) (fvΣty-low A n e)

  fvΣty← : ∀ A m → Mem m (fvTy A) → Mem (S m) (fvTy (Σty A))
  fvΣty← (arr A t u) m p with mem++ m (fvTy A) (fvTm t ++ fvTm u) p
  ... | inj₁ q = mem++l (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) (fvΣty← A m q)
  ... | inj₂ q with mem++ m (fvTm t) (fvTm u) q
  ...   | inj₁ r = mem++r (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u))
                     (mem++l (S m) (fvTm (Σtm t)) (fvTm (Σtm u)) (fvΣtm← t m r))
  ...   | inj₂ r = mem++r (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u))
                     (mem++r (S m) (fvTm (Σtm t)) (fvTm (Σtm u)) (fvΣtm← u m r))

  fvΣtm← : ∀ t m → Mem m (fvTm t) → Mem (S m) (fvTm (Σtm t))
  fvΣtm← (var i)     m p = subst (λ k → Mem (S k) (S i ∷ [])) (sym (mem-single m i p)) (mem-here (S i) [])
  fvΣtm← (coh Θ A τ) m p = fvΣsub← τ m p

  fvΣsub← : ∀ σ m → Mem m (fvSub σ) → Mem (S m) (fvSub (Σsub σ))
  fvΣsub← (σ ,ₛ t) m p with mem++ m (fvSub σ) (fvTm t) p
  ... | inj₁ q = mem++l (S m) (fvSub (Σsub σ)) (fvTm (Σtm t)) (fvΣsub← σ m q)
  ... | inj₂ q = mem++r (S m) (fvSub (Σsub σ)) (fvTm (Σtm t)) (fvΣtm← t m q)

fvΣ→ : ∀ t A n → Mem n (fvTmTy (Σtm t) (Σty A)) → LMem n (fvTmTy t A)
fvΣ→ t A n p with mem++ n (fvTm (Σtm t)) (fvTy (Σty A)) p
... | inj₁ q = LMem-map (fvTm t) (fvTmTy t A) (λ m r → mem++l m (fvTm t) (fvTy A) r) (fvΣtm→ t n q)
... | inj₂ q = LMem-map (fvTy A) (fvTmTy t A) (λ m r → mem++r m (fvTm t) (fvTy A) r) (fvΣty→ A n q)

fvΣ← : ∀ t A n → LMem n (fvTmTy t A) → Mem n (fvTmTy (Σtm t) (Σty A))
fvΣ← t A n (inj₁ e)        = mem++r n (fvTm (Σtm t)) _ (fvΣty-low A n (inj₁ e))
fvΣ← t A n (inj₂ (inj₁ e)) = mem++r n (fvTm (Σtm t)) _ (fvΣty-low A n (inj₂ e))
fvΣ← t A .(S m) (inj₂ (inj₂ (m , refl , p))) with mem++ m (fvTm t) _ p
... | inj₁ q = mem++l (S m) (fvTm (Σtm t)) _ (fvΣtm← t m q)
... | inj₂ q = mem++r (S m) (fvTm (Σtm t)) _ (fvΣty← A m q)

------------------------------------------------------------------------
-- Lengths, lookups, boundaries and dimension of suspended contexts.

lenΣ : ∀ Γ → len (Σctx Γ) ≡ S (len Γ)
lenΣ ε       = refl
lenΣ (Γ ▸ A) = cong suc (lenΣ Γ)

lenₛΣ : ∀ σ → lenₛ (Σsub σ) ≡ S (lenₛ σ)
lenₛΣ ⟨⟩       = refl
lenₛΣ (σ ,ₛ t) = cong suc (lenₛΣ σ)

dimΣ : ∀ A → dim (Σty A) ≡ suc (dim A)
dimΣ ⋆           = refl
dimΣ (arr A t u) = cong suc (dimΣ A)

lookupΣ : ∀ Γ i {A} → lookup Γ i ≡ just A → lookup (Σctx Γ) (S i) ≡ just (Σty A)
lookupΣ (Γ ▸ B) i eq rewrite lenΣ Γ with i ==ℕ len Γ
... | true  = cong (λ X → just (Σty X)) (just-inj eq)
... | false = lookupΣ Γ i eq

lookupΣ-N : ∀ Γ → lookup (Σctx Γ) 0 ≡ just ⋆
lookupΣ-N ε       = refl
lookupΣ-N (Γ ▸ A) rewrite lenΣ Γ = lookupΣ-N Γ

lookupΣ-S : ∀ Γ → lookup (Σctx Γ) 1 ≡ just ⋆
lookupΣ-S ε       = refl
lookupΣ-S (Γ ▸ A) rewrite lenΣ Γ = lookupΣ-S Γ

lookupₛΣ : ∀ σ i → lookupₛ (Σsub σ) (S i) ≡ Σtm (lookupₛ σ i)
lookupₛΣ ⟨⟩       i = refl
lookupₛΣ (σ ,ₛ t) i rewrite lenₛΣ σ with i ==ℕ lenₛ σ
... | true  = refl
... | false = lookupₛΣ σ i

lookupₛΣ-N : ∀ σ → lookupₛ (Σsub σ) 0 ≡ var 0
lookupₛΣ-N ⟨⟩       = refl
lookupₛΣ-N (σ ,ₛ t) rewrite lenₛΣ σ = lookupₛΣ-N σ

lookupₛΣ-S : ∀ σ → lookupₛ (Σsub σ) 1 ≡ var 1
lookupₛΣ-S ⟨⟩       = refl
lookupₛΣ-S (σ ,ₛ t) rewrite lenₛΣ σ = lookupₛΣ-S σ

srcΣ : ∀ i Γ → srcVars (suc i) (Σctx Γ) ≡ Lift (srcVars i Γ)
srcΣ i ε           = refl
srcΣ i (ε ▸ A)     = refl
srcΣ i (Γ ▸ A ▸ B) rewrite dimΣ A | lenΣ Γ | srcΣ i Γ with i <ℕ suc (dim A)
... | true  = refl
... | false = cong (λ X → 0 ∷ 1 ∷ X)
                (sym (trans (mapS-++ (srcVars i Γ ++ (len Γ ∷ [])) (suc (len Γ) ∷ []))
                            (cong (_++ (S (suc (len Γ)) ∷ [])) (mapS-++ (srcVars i Γ) (len Γ ∷ [])))))

data Odd : Ctx → Set where
  odd₁ : ∀ {A} → Odd (ε ▸ A)
  odd+ : ∀ {Γ A B} → Odd Γ → Odd (Γ ▸ A ▸ B)

private
  data NE : List Nat → Set where
    ne : ∀ {x xs} → NE (x ∷ xs)

  NE-if : ∀ {xs ys} b → NE xs → NE ys → NE (if b then xs else ys)
  NE-if true  p _ = p
  NE-if false _ q = q

  NE-snoc : ∀ xs y → NE (xs ++ (y ∷ []))
  NE-snoc []       y = ne
  NE-snoc (x ∷ xs) y = ne

  tgt-NE : ∀ i Γ → Odd Γ → NE (tgtVars i Γ)
  tgt-NE i (ε ▸ A) odd₁ = ne
  tgt-NE i (Γ ▸ A ▸ B) (odd+ o) =
    NE-if (i <ℕ dim A) (tgt-NE i Γ o)
      (NE-if (dim A ==ℕ i) (NE-snoc _ (len Γ)) (NE-snoc (tgtVars i Γ ++ (len Γ ∷ [])) (suc (len Γ))))

  dropLast-Lift : ∀ xs → NE xs → dropLast (Lift xs) ≡ Lift (dropLast xs)
  dropLast-Lift (x ∷ xs) ne = cong (λ X → 0 ∷ 1 ∷ X) (sym (mapS-dropLast (x ∷ xs)))

tgtΣ : ∀ i Γ → Odd Γ → tgtVars (suc i) (Σctx Γ) ≡ Lift (tgtVars i Γ)
tgtΣ i (ε ▸ A) odd₁ = refl
tgtΣ i (Γ ▸ A ▸ B) (odd+ o) rewrite dimΣ A | lenΣ Γ | tgtΣ i Γ o with i <ℕ dim A
... | true  = refl
... | false with dim A ==ℕ i
...   | true  = trans (cong (_++ (S (len Γ) ∷ [])) (dropLast-Lift (tgtVars i Γ) (tgt-NE i Γ o)))
                      (cong (λ X → 0 ∷ 1 ∷ X) (sym (mapS-++ (dropLast (tgtVars i Γ)) (len Γ ∷ []))))
...   | false = cong (λ X → 0 ∷ 1 ∷ X)
                  (sym (trans (mapS-++ (tgtVars i Γ ++ (len Γ ∷ [])) (suc (len Γ) ∷ []))
                              (cong (_++ (S (suc (len Γ)) ∷ [])) (mapS-++ (tgtVars i Γ) (len Γ ∷ [])))))

dimCtxΣ : ∀ Γ → Odd Γ → dimCtx (Σctx Γ) ≡ suc (dimCtx Γ)
dimCtxΣ (ε ▸ A) odd₁ rewrite dimΣ A | max-0 (dim A) = refl
dimCtxΣ (Γ ▸ A ▸ B) (odd+ o) rewrite dimΣ A | dimΣ B | dimCtxΣ Γ o = refl

------------------------------------------------------------------------
-- Pasting contexts.

ps-odd : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Odd Γ
ps-odd pss     = odd₁
ps-odd (pse d) = odd+ (ps-odd d)
ps-odd (psd d) = ps-odd d

private
  pse-at : ∀ {Γ x A n} → n ≡ len Γ → Γ ⊢ps x ∶ A →
           (Γ ▸ A ▸ arr A (var x) (var n)) ⊢ps suc n ∶ arr A (var x) (var n)
  pse-at refl d = pse d

Σps : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Σctx Γ ⊢ps S x ∶ Σty A
Σps pss                 = pse pss
Σps (pse {Γ} d)         = pse-at (sym (lenΣ Γ)) (Σps d)
Σps (psd d)             = psd (Σps d)

Σps′ : ∀ {Γ} → Γ ⊢ps → Σctx Γ ⊢ps
Σps′ (ps d) = ps (psd (Σps d))

-- A pasting context of dimension 0 is the point.
ps-dim0 : ∀ {Γ x A} → Γ ⊢ps x ∶ A → dimCtx Γ ≡ 0 → Γ ≡ ε ▸ ⋆
ps-dim0 pss     _ = refl
ps-dim0 (pse {Γ} {x} {A} d) e = ⊥-elim (max-suc (dim A) (dimCtx (Γ ▸ A)) e)
  where
  max-suc : ∀ m n → max (suc m) n ≡ 0 → ⊥
  max-suc m zero    ()
  max-suc m (suc n) ()
ps-dim0 (psd d) e = ps-dim0 d e

------------------------------------------------------------------------
-- The side condition is preserved.

memDown : ∀ n k → Mem n (downFrom k) → T (n <ℕ k)
memDown n (suc k) p with mem-cons n k (downFrom k) p
... | inj₁ refl = lt n
  where
  lt : ∀ n → T (n <ℕ suc n)
  lt zero = tt
  lt (suc n) = lt n
... | inj₂ q = <-suc n k (memDown n k q)

downMem : ∀ n k → T (n <ℕ k) → Mem n (downFrom k)
downMem n (suc k) p with n ==ℕ k in e
... | true  = tt
... | false = downMem n k (lt′ n k p e)
  where
  lt′ : ∀ n k → T (n <ℕ suc k) → (n ==ℕ k) ≡ false → T (n <ℕ k)
  lt′ zero    zero    _ ()
  lt′ zero    (suc k) _ _ = tt
  lt′ (suc n) zero    p _ = ⊥-elim (no n p)
    where
    no : ∀ n → T (n <ℕ zero) → ⊥
    no _ ()
  lt′ (suc n) (suc k) p q = lt′ n k p q

private
  vars→ : ∀ Γ n → Mem n (varsCtx (Σctx Γ)) → LMem n (varsCtx Γ)
  vars→ Γ zero          _ = inj₁ refl
  vars→ Γ (suc zero)    _ = inj₂ (inj₁ refl)
  vars→ Γ (suc (suc m)) p =
    inj₂ (inj₂ (m , refl , downMem m (len Γ) (subst (λ k → T (S m <ℕ k)) (lenΣ Γ) (memDown (S m) (len (Σctx Γ)) p))))

  vars← : ∀ Γ n → LMem n (varsCtx Γ) → Mem n (varsCtx (Σctx Γ))
  vars← Γ .0 (inj₁ refl) = downMem 0 (len (Σctx Γ)) (subst (λ k → T (0 <ℕ k)) (sym (lenΣ Γ)) tt)
  vars← Γ .1 (inj₂ (inj₁ refl)) = downMem 1 (len (Σctx Γ)) (subst (λ k → T (1 <ℕ k)) (sym (lenΣ Γ)) tt)
  vars← Γ .(S m) (inj₂ (inj₂ (m , refl , p))) =
    downMem (S m) (len (Σctx Γ)) (subst (λ k → T (S m <ℕ k)) (sym (lenΣ Γ)) (memDown m (len Γ) p))

  isCohΣ : ∀ Θ A t u → T (isCoh Θ A t u) → T (isCoh (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  isCohΣ Θ A t u p = and {≈? (fvTmTy (Σtm t) (Σty A)) (varsCtx (Σctx Θ))}
    (lift-≈ (fvTmTy t A) (varsCtx Θ) (fvTmTy (Σtm t) (Σty A)) (varsCtx (Σctx Θ))
            (∧-fst p) (fvΣ→ t A) (fvΣ← t A) (vars→ Θ) (vars← Θ))
    (lift-≈ (fvTmTy u A) (varsCtx Θ) (fvTmTy (Σtm u) (Σty A)) (varsCtx (Σctx Θ))
            (∧-snd {≈? (fvTmTy t A) (varsCtx Θ)} p)
            (fvΣ→ u A) (fvΣ← u A) (vars→ Θ) (vars← Θ))
    where
    and : ∀ {a b} → T a → T b → T (a ∧ b)
    and {true} _ q = q

  Lift-eq→ : ∀ {X Xs} → Xs ≡ Lift X → ∀ n → Mem n Xs → LMem n X
  Lift-eq→ {X} refl n p = Lift→ n X p

  Lift-eq← : ∀ {X Xs} → Xs ≡ Lift X → ∀ n → LMem n X → Mem n Xs
  Lift-eq← {X} refl n p = Lift← n X p

  isOpΣ : ∀ Θ d A t u → Odd Θ → dimCtx Θ ≡ suc d → T (isOp Θ A t u) →
          T (isOp (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  isOpΣ Θ d A t u o e p = and {≈? (fvTmTy (Σtm t) (Σty A)) (∂⁻ (Σctx Θ))}
    (lift-≈ (fvTmTy t A) (∂⁻ Θ) (fvTmTy (Σtm t) (Σty A)) (∂⁻ (Σctx Θ))
            (∧-fst p) (fvΣ→ t A) (fvΣ← t A) (Lift-eq→ src) (Lift-eq← src))
    (lift-≈ (fvTmTy u A) (∂⁺ Θ) (fvTmTy (Σtm u) (Σty A)) (∂⁺ (Σctx Θ))
            (∧-snd {≈? (fvTmTy t A) (∂⁻ Θ)} p)
            (fvΣ→ u A) (fvΣ← u A) (Lift-eq→ tgt) (Lift-eq← tgt))
    where
    and : ∀ {a b} → T a → T b → T (a ∧ b)
    and {true} _ q = q
    dimeq : dimCtx (Σctx Θ) ∸ 1 ≡ suc (dimCtx Θ ∸ 1)
    dimeq rewrite dimCtxΣ Θ o | e = refl
    src : ∂⁻ (Σctx Θ) ≡ Lift (∂⁻ Θ)
    src rewrite dimeq = srcΣ (dimCtx Θ ∸ 1) Θ
    tgt : ∂⁺ (Σctx Θ) ≡ Lift (∂⁺ Θ)
    tgt rewrite dimeq = tgtΣ (dimCtx Θ ∸ 1) Θ o

  -- Over the point, an operation is a full coherence.
  op→coh-D₀ : ∀ A t u → T (isOp (ε ▸ ⋆) A t u) → T (isCoh (ε ▸ ⋆) A t u)
  op→coh-D₀ A t u p = p

  ∨-elim : ∀ {a b} {P : Set} → T (a ∨ b) → (T a → P) → (T b → P) → P
  ∨-elim {true}          p f g = f tt
  ∨-elim {false} {true}  p f g = g tt

  ∨-inl : ∀ {a b} → T a → T (a ∨ b)
  ∨-inl {true} _ = tt

  ∨-inr : ∀ {a b} → T b → T (a ∨ b)
  ∨-inr {true}  _ = tt
  ∨-inr {false} p = p

sideΣ : ∀ {Θ A t u} → Θ ⊢ps → T (cattSide Θ A t u) →
        T (cattSide (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
sideΣ {Θ} {A} {t} {u} (ps d) p = go (dimCtx Θ) refl
  where
  go : ∀ n → dimCtx Θ ≡ n → T (cattSide (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  go zero    e = ∨-inl (isCohΣ Θ A t u (subst (λ Γ → T (cattSide Γ A t u) → T (isCoh Γ A t u))
                                               (sym (ps-dim0 d e))
                                               (λ q → ∨-elim q (λ c → c) (op→coh-D₀ A t u)) p))
  go (suc k) e = ∨-elim p (λ c → ∨-inl (isCohΣ Θ A t u c))
                          (λ o → ∨-inr (isOpΣ Θ k A t u (ps-odd d) e o))

------------------------------------------------------------------------
-- Suspension commutes with substitution.

mutual
  Σty[] : ∀ A σ → Σty (A [ σ ]ty) ≡ Σty A [ Σsub σ ]ty
  Σty[] ⋆           σ = sym (cong₂ (arr ⋆) (lookupₛΣ-N σ) (lookupₛΣ-S σ))
  Σty[] (arr A t u) σ =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y)) (Σty[] A σ) (cong₂ _,_ (Σtm[] t σ) (Σtm[] u σ))

  Σtm[] : ∀ t σ → Σtm (t [ σ ]tm) ≡ Σtm t [ Σsub σ ]tm
  Σtm[] (var i)     σ = sym (lookupₛΣ σ i)
  Σtm[] (coh Θ A τ) σ = cong (coh (Σctx Θ) (Σty A)) (Σsub∘ τ σ)
  Σtm[] (cst k)     σ = refl

  Σsub∘ : ∀ τ σ → Σsub (τ ∘ σ) ≡ Σsub τ ∘ Σsub σ
  Σsub∘ ⟨⟩       σ = sym (cong₂ (λ a b → ⟨⟩ ,ₛ a ,ₛ b) (lookupₛΣ-N σ) (lookupₛΣ-S σ))
  Σsub∘ (τ ,ₛ t) σ = cong₂ _,ₛ_ (Σsub∘ τ σ) (Σtm[] t σ)

------------------------------------------------------------------------
-- The theorem.

private
  N-wf : ∀ {Γ} → Σctx Γ ⊢ctx → Σctx Γ ⊢ty Σty ⋆
  N-wf {Γ} w = arr-wf (var-wf w (lookupΣ-N Γ)) (var-wf w (lookupΣ-S Γ))

mutual
  Σctx-wf : ∀ {Γ} → Γ ⊢ctx → FNcCtx Γ → Σctx Γ ⊢ctx
  Σctx-wf ε-wf _ = ▸-wf (▸-wf ε-wf (⋆-wf ε-wf)) (⋆-wf (▸-wf ε-wf (⋆-wf ε-wf)))
  Σctx-wf (▸-wf w a) (nΓ , nA) = ▸-wf (Σctx-wf w nΓ) (Σty-wf a nΓ nA)

  Σty-wf : ∀ {Γ A} → Γ ⊢ty A → FNcCtx Γ → FNcTy A → Σctx Γ ⊢ty Σty A
  Σty-wf (⋆-wf w) nΓ _ = N-wf (Σctx-wf w nΓ)
  Σty-wf (arr-wf d e) nΓ (_ , nt , nu) = arr-wf (Σtm-wf d nΓ nt) (Σtm-wf e nΓ nu)

  Σtm-wf : ∀ {Γ t A} → Γ ⊢tm t ∶ A → FNcCtx Γ → FNcTm t → Σctx Γ ⊢tm Σtm t ∶ Σty A
  Σtm-wf {Γ} (var-wf {i} w eq) nΓ _ = var-wf (Σctx-wf w nΓ) (lookupΣ Γ i eq)
  Σtm-wf {Γ} (coh-wf {Θ} {A} {t} {u} {σ} p w a ok s) nΓ (nΘ , (nA , nt , nu) , nσ) =
    subst (Σctx Γ ⊢tm coh (Σctx Θ) (Σty (arr A t u)) (Σsub σ) ∶_)
      (sym (Σty[] (arr A t u) σ))
      (coh-wf (Σps′ p) (Σctx-wf w nΘ) (Σty-wf a nΘ (nA , nt , nu)) (sideΣ {Θ} {A} {t} {u} p ok) (Σsub-wf s nΓ nσ))
  Σtm-wf (cst-wf _ _) _ ()

  Σsub-wf : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → FNcCtx Γ → FNcSub σ → Σctx Γ ⊢sub Σsub σ ∶ Σctx Δ
  Σsub-wf {Γ} (⟨⟩-wf w) nΓ _ =
    ,-wf (,-wf (⟨⟩-wf w′) (var-wf w′ (lookupΣ-N Γ))) (var-wf w′ (lookupΣ-S Γ))
    where
    w′ = Σctx-wf w nΓ
  Σsub-wf {Γ} (,-wf {σ} {Δ} {t} {A} s d) nΓ (nσ , nt) =
    ,-wf (Σsub-wf s nΓ nσ) (subst (Σctx Γ ⊢tm Σtm t ∶_) (Σty[] A σ) (Σtm-wf d nΓ nt))

------------------------------------------------------------------------
-- Elements elaboration: a derivation over Γ, suspended, lands in any
-- context Δ that interprets ΣΓ (N, S and Γ's variables one dimension
-- up), by substitution admissibility.

module _ (closed : Sb.Closed) where
  elements : ∀ {Γ Δ t A γ} → Γ ⊢tm t ∶ A → FNcCtx Γ → FNcTm t →
             Δ ⊢sub γ ∶ Σctx Γ → Δ ⊢tm Σtm t [ γ ]tm ∶ Σty A [ γ ]ty
  elements d nΓ nt g = Sb.tm[] closed (Σtm-wf d nΓ nt) g
