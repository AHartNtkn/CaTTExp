------------------------------------------------------------------------
-- Soundness of CaTT (over a signature) for a class of strict models:
-- one-object, locally discrete strict ω-categories whose 1-cells form a
-- group (ledger item A3, first step). Used for A4 in
-- CaTTExp.Sketch.NonDerivable.
--
-- The model. Fix a group G. The strict ω-category B G has one object,
-- G as its 1-cells, and only identity cells above dimension 1. So in
-- B G:
--   * a 1-cell type x → y is always inhabited (any element of G);
--   * a 2-cell type f ⇒ g is inhabited exactly when f = g in G;
--   * every type of dimension ≥ 3 is inhabited (by identities).
-- Constants are interpreted by a function M : K → G, and must satisfy
-- the model's 2-cell condition when their type is a 2-cell type.
--
-- The interpretation ⟦_⟧ sends a term to an element of G (its value as
-- a 1-cell; the value of objects and higher cells is irrelevant). A
-- coherence of 1-dimensional type x → y over a pasting context Θ is
-- interpreted as the composite along Θ from x to y, computed with the
-- *potential* `pot` of the objects of Θ: pot(x₀) = e and
-- pot(y) = pot(x) · f for each attached arrow f : x → y.
--
-- The theorem (`sound`): if Γ ⊢ t ∶ A and ρ is a valid environment for
-- Γ (it satisfies the 2-cell condition for every 2-cell variable of Γ)
-- then A is inhabited in B G at ρ; for a 2-cell type f ⇒ g this says
-- ⟦f⟧ρ = ⟦g⟧ρ.
--
-- The heart of the proof is the 1-dimensional contractibility of
-- pasting contexts in B G: in a pasting context Θ with a valid
-- environment, every 1-cell term between objects x and y has value
-- pot(x)⁻¹ · pot(y) (lemma `val`). Constants of type ⋆ complicate this,
-- because a 1-cell term in Θ may run between two constant objects. The
-- syntactic lemma `dich` shows that such a term mentions no variable
-- at all, so the side condition of the coh rule can never be met by
-- it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.GroupModel (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Subst 𝕊 cattSide
open import CaTTExp.PastingCheck 𝕊 using (PsTy; ⋆ₚ; arrₚ; ps-ty)

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

------------------------------------------------------------------------
-- Arithmetic.

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

  <-suc-self : ∀ n → T (n <ℕ suc n)
  <-suc-self zero    = tt
  <-suc-self (suc n) = <-suc-self n

  ==→≡ : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
  ==→≡ i n p = ==ℕ-sound i n (≡→T p)

  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl n = T→≡ (==ℕ-refl n)

  <suc-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  <suc-≢ zero    zero    _ ()
  <suc-≢ zero    (suc n) _ _ = tt
  <suc-≢ (suc i) zero    p _ = ⊥-elim (no i p)
    where
    no : ∀ i → T (i <ℕ zero) → ⊥
    no _ ()
  <suc-≢ (suc i) (suc n) p q = <suc-≢ i n p q

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  ⋆≢arr : ∀ {A t u} → just ⋆ ≡ just (arr A t u) → ⊥
  ⋆≢arr ()

------------------------------------------------------------------------
-- Lookup.

lookup-top : ∀ Γ A → lookup (Γ ▸ A) (len Γ) ≡ just A
lookup-top Γ A rewrite ==-refl (len Γ) = refl

lookup-wk : ∀ {Γ i} B → T (i <ℕ len Γ) → lookup (Γ ▸ B) i ≡ lookup Γ i
lookup-wk {Γ} {i} B p rewrite <→≢ i (len Γ) p = refl

lookup-< : ∀ Γ i {A} → lookup Γ i ≡ just A → T (i <ℕ len Γ)
lookup-< (Γ ▸ B) i eq with i ==ℕ len Γ in e
... | true  rewrite ==→≡ i (len Γ) e = <-suc-self (len Γ)
... | false = <-suc i (len Γ) (lookup-< Γ i eq)

lookup-wk′ : ∀ Γ i {A} B → lookup Γ i ≡ just A → lookup (Γ ▸ B) i ≡ just A
lookup-wk′ Γ i B eq = trans (lookup-wk {Γ} {i} B (lookup-< Γ i eq)) eq

lookupₛ-top : ∀ σ s → lookupₛ (σ ,ₛ s) (lenₛ σ) ≡ s
lookupₛ-top σ s rewrite ==-refl (lenₛ σ) = refl

lookupₛ-wk : ∀ σ s i → T (i <ℕ lenₛ σ) → lookupₛ (σ ,ₛ s) i ≡ lookupₛ σ i
lookupₛ-wk σ s i p rewrite <→≢ i (lenₛ σ) p = refl

------------------------------------------------------------------------
-- Objects, bases and closed syntax.

-- `a` is a variable of type ⋆ in Γ.
Obj : Ctx → Tm → Set
Obj Γ a = Σ Nat λ i → (a ≡ var i) × (lookup Γ i ≡ just ⋆)

-- The 0-dimensional source and target of a type of positive dimension.
data Base : Ty → Tm → Tm → Set where
  base1 : ∀ {a b} → Base (arr ⋆ a b) a b
  base+ : ∀ {A t u a b} → Base A a b → Base (arr A t u) a b

Base-[] : ∀ {A a b} σ → Base A a b → Base (A [ σ ]ty) (a [ σ ]tm) (b [ σ ]tm)
Base-[] σ base1     = base1
Base-[] σ (base+ r) = base+ (Base-[] σ r)

Base-inv : ∀ A σ {a b} → Base (A [ σ ]ty) a b →
           Σ Tm λ a′ → Σ Tm λ b′ → Base A a′ b′ × (a ≡ a′ [ σ ]tm) × (b ≡ b′ [ σ ]tm)
Base-inv (arr ⋆ t u)           σ base1     = t , u , base1 , refl , refl
Base-inv (arr (arr A x y) t u) σ (base+ r) =
  let (a′ , b′ , r′ , ea , eb) = Base-inv (arr A x y) σ r in a′ , b′ , base+ r′ , ea , eb

Base-sc : ∀ {n A a b} → ScTy n A → Base A a b → ScTm n a × ScTm n b
Base-sc (_ , p , q) base1     = p , q
Base-sc (a , _ , _) (base+ r) = Base-sc a r

PsTy-base : ∀ {A} → PsTy A → (A ≡ ⋆) ⊎ (Σ Nat λ i → Σ Nat λ j → Base A (var i) (var j))
PsTy-base ⋆ₚ                  = inj₁ refl
PsTy-base (arrₚ {x = x} {y} ⋆ₚ) = inj₂ (x , y , base1)
PsTy-base (arrₚ p@(arrₚ _))   with PsTy-base p
... | inj₂ (i , j , r) = inj₂ (i , j , base+ r)

closed-not-var : ∀ {i} → ScTm 0 (var i) → ⊥
closed-not-var ()

-- Terms of type ⋆ are variables or constants.
star-inv′ : ∀ {Γ t A} → Γ ⊢tm t ∶ A → A ≡ ⋆ → Obj Γ t ⊎ (Σ K λ k → t ≡ cst k)
star-inv′ (var-wf {i} _ e) refl = inj₁ (i , refl , e)
star-inv′ (cst-wf {k} _ _) _    = inj₂ (k , refl)
star-inv′ (coh-wf _ _ _ _ _) ()

star-inv : ∀ {Γ t} → Γ ⊢tm t ∶ ⋆ → Obj Γ t ⊎ (Σ K λ k → t ≡ cst k)
star-inv d = star-inv′ d refl

-- Closed syntax has no free variables.
mutual
  fv0-ty : ∀ A → ScTy 0 A → fvTy A ≡ []
  fv0-ty ⋆           _           = refl
  fv0-ty (arr A t u) (a , p , q) rewrite fv0-ty A a | fv0-tm t p | fv0-tm u q = refl

  fv0-tm : ∀ t → ScTm 0 t → fvTm t ≡ []
  fv0-tm (var i)     ()
  fv0-tm (coh _ _ σ) p = fv0-sub σ p
  fv0-tm (cst _)     _ = refl

  fv0-sub : ∀ σ → ScSub 0 σ → fvSub σ ≡ []
  fv0-sub ⟨⟩       _       = refl
  fv0-sub (σ ,ₛ t) (p , q) rewrite fv0-sub σ p | fv0-tm t q = refl

------------------------------------------------------------------------
-- Facts about pasting contexts.

-- Every arrow variable's endpoints are variables of the next type down.
ArrInv : Ctx → Set
ArrInv Γ = ∀ f A x y → lookup Γ f ≡ just (arr A (var x) (var y)) →
           (lookup Γ x ≡ just A) × (lookup Γ y ≡ just A)

PsInv : Ctx → Set
PsInv Γ = ∀ f A → lookup Γ f ≡ just A → PsTy A

private
  arrInv-wk : ∀ {Γ} B → ArrInv Γ → ∀ f A x y → T (f <ℕ len Γ) →
              lookup (Γ ▸ B) f ≡ just (arr A (var x) (var y)) →
              (lookup (Γ ▸ B) x ≡ just A) × (lookup (Γ ▸ B) y ≡ just A)
  arrInv-wk {Γ} B I f A x y p eq =
    let (ex , ey) = I f A x y (trans (sym (lookup-wk {Γ} {f} B p)) eq) in
    lookup-wk′ Γ x B ex , lookup-wk′ Γ y B ey

private
  inv-top : ∀ {L : Nat → Maybe Ty} {A x n C y z} → L x ≡ just A → L n ≡ just A →
            arr A (var x) (var n) ≡ arr C (var y) (var z) → (L y ≡ just C) × (L z ≡ just C)
  inv-top ex en refl = ex , en

ps-facts : ∀ {Γ x A} → Γ ⊢ps x ∶ A → (lookup Γ x ≡ just A) × ArrInv Γ × PsInv Γ
ps-facts pss = refl , inv , psinv
  where
  inv : ArrInv (ε ▸ ⋆)
  inv f A x y eq with f ==ℕ 0
  inv f A x y () | true
  inv f A x y () | false
  psinv : PsInv (ε ▸ ⋆)
  psinv f A eq with f ==ℕ 0
  psinv f A refl | true = ⋆ₚ
  psinv f A ()   | false
ps-facts (psd d) =
  let (ef , I , P) = ps-facts d in snd (I _ _ _ _ ef) , I , P
ps-facts {Γ ▸ A ▸ B} (pse {Γ} {x} {A} d) = top , inv , psinv
  where
  facts = ps-facts d
  ex : lookup Γ x ≡ just A
  ex = fst facts
  I : ArrInv Γ
  I = fst (snd facts)
  P : PsInv Γ
  P = snd (snd facts)
  n = len Γ

  top : lookup (Γ ▸ A ▸ B) (suc n) ≡ just B
  top = lookup-top (Γ ▸ A) B

  eA : lookup (Γ ▸ A ▸ B) n ≡ just A
  eA = trans (lookup-wk {Γ ▸ A} {n} B (<-suc-self n)) (lookup-top Γ A)

  ex′ : lookup (Γ ▸ A ▸ B) x ≡ just A
  ex′ = lookup-wk′ (Γ ▸ A) x B (lookup-wk′ Γ x A ex)

  wk2 : ∀ i {C} → lookup Γ i ≡ just C → lookup (Γ ▸ A ▸ B) i ≡ just C
  wk2 i e = lookup-wk′ (Γ ▸ A) i B (lookup-wk′ Γ i A e)

  inv : ArrInv (Γ ▸ A ▸ B)
  inv f C y z eq with f ==ℕ suc n in e₁
  ... | true  = inv-top ex′ eA (just-inj eq)
  ... | false with f ==ℕ n in e₂
  ...   | true =
    -- f is the new variable n : A, and A is the type of x.
    let (ey , ez) = I x C y z (trans ex eq) in wk2 y ey , wk2 z ez
  ...   | false =
    let (ey , ez) = I f C y z eq in wk2 y ey , wk2 z ez

  psinv : PsInv (Γ ▸ A ▸ B)
  psinv f C eq with f ==ℕ suc n
  ... | true = subst PsTy (just-inj eq) (arrₚ (ps-ty d))
  ... | false with f ==ℕ n
  ...   | true  = subst PsTy (just-inj eq) (ps-ty d)
  ...   | false = P f C eq

-- The endpoints of a variable's type are objects.
base-obj : ∀ {Γ f A a b} → ArrInv Γ → PsInv Γ → lookup Γ f ≡ just A → Base A a b →
           Obj Γ a × Obj Γ b
base-obj {Γ} {f} {A} I P eq r with P f A eq
base-obj {Γ} {f} {arr ⋆ (var x) (var y)} I P eq base1 | arrₚ _ =
  let (ex , ey) = I f ⋆ x y eq in (x , refl , ex) , (y , refl , ey)
base-obj {Γ} {f} {arr (arr A s t) (var x) (var y)} I P eq (base+ r) | arrₚ _ =
  base-obj {Γ} {x} I P (fst (I f (arr A s t) x y eq)) r

ps-scope : ∀ {Γ x A} → Γ ⊢ps x ∶ A → T (x <ℕ len Γ)
ps-scope {Γ} {x} d = lookup-< Γ x (fst (ps-facts d))

-- Variable sets of a pasting context are non-empty.
data NE : List Nat → Set where
  ne : ∀ {x xs} → NE (x ∷ xs)

private
  NE-snoc : ∀ xs y → NE (xs ++ (y ∷ []))
  NE-snoc []       y = ne
  NE-snoc (x ∷ xs) y = ne

  NE-if : ∀ {xs ys} b → NE xs → NE ys → NE (if b then xs else ys)
  NE-if true  p _ = p
  NE-if false _ q = q

ps-src-NE : ∀ {Γ x A} i → Γ ⊢ps x ∶ A → NE (srcVars i Γ)
ps-src-NE i pss = ne
ps-src-NE i (psd d) = ps-src-NE i d
ps-src-NE i (pse {Γ} {x} {A} d) =
  NE-if (i <ℕ suc (dim A)) (ps-src-NE i d) (NE-snoc (srcVars i Γ ++ (len Γ ∷ [])) (suc (len Γ)))

ps-tgt-NE : ∀ {Γ x A} i → Γ ⊢ps x ∶ A → NE (tgtVars i Γ)
ps-tgt-NE i pss = ne
ps-tgt-NE i (psd d) = ps-tgt-NE i d
ps-tgt-NE i (pse {Γ} {x} {A} d) =
  NE-if (i <ℕ dim A) (ps-tgt-NE i d)
    (NE-if (dim A ==ℕ i) (NE-snoc _ (len Γ)) (NE-snoc (tgtVars i Γ ++ (len Γ ∷ [])) (suc (len Γ))))

ps-vars-NE : ∀ {Γ x A} → Γ ⊢ps x ∶ A → NE (varsCtx Γ)
ps-vars-NE pss     = ne
ps-vars-NE (pse d) = ne
ps-vars-NE (psd d) = ps-vars-NE d

-- The coh side condition fails when one side mentions no variable.
private
  ≈?-[]-NE : ∀ {V} → NE V → ≈? [] V ≡ false
  ≈?-[]-NE ne = refl

  side-fail : ∀ (L V S X Y : Bool) → L ≡ false → S ≡ false →
              T ((L ∧ X) ∨ (S ∧ Y)) → ⊥
  side-fail L V S X Y refl refl ()

  side-fail′ : ∀ (L V S X Y : Bool) → L ≡ false → S ≡ false →
               T ((X ∧ L) ∨ (Y ∧ S)) → ⊥
  side-fail′ L V S true true refl refl ()
  side-fail′ L V S true false refl refl ()
  side-fail′ L V S false true refl refl ()
  side-fail′ L V S false false refl refl ()

side-t-empty : ∀ {Θ B t u} → Θ ⊢ps → fvTmTy t B ≡ [] → T (cattSide Θ B t u) → ⊥
side-t-empty {Θ} {B} {t} {u} (ps d) e ok =
  side-fail (≈? (fvTmTy t B) (varsCtx Θ)) true (≈? (fvTmTy t B) (∂⁻ Θ))
            (≈? (fvTmTy u B) (varsCtx Θ)) (≈? (fvTmTy u B) (∂⁺ Θ))
            (trans (cong (λ L → ≈? L (varsCtx Θ)) e) (≈?-[]-NE (ps-vars-NE d)))
            (trans (cong (λ L → ≈? L (∂⁻ Θ)) e) (≈?-[]-NE (ps-src-NE (dimCtx Θ ∸ 1) d)))
            ok

side-u-empty : ∀ {Θ B t u} → Θ ⊢ps → fvTmTy u B ≡ [] → T (cattSide Θ B t u) → ⊥
side-u-empty {Θ} {B} {t} {u} (ps d) e ok =
  side-fail′ (≈? (fvTmTy u B) (varsCtx Θ)) true (≈? (fvTmTy u B) (∂⁺ Θ))
             (≈? (fvTmTy t B) (varsCtx Θ)) (≈? (fvTmTy t B) (∂⁻ Θ))
             (trans (cong (λ L → ≈? L (varsCtx Θ)) e) (≈?-[]-NE (ps-vars-NE d)))
             (trans (cong (λ L → ≈? L (∂⁺ Θ)) e) (≈?-[]-NE (ps-tgt-NE (dimCtx Θ ∸ 1) d)))
             ok

private
  base-not-⋆ : ∀ {A a b} → Base A a b → A ≡ ⋆ → ⊥
  base-not-⋆ base1     ()
  base-not-⋆ (base+ _) ()

  fvTmTy-0 : ∀ {t B} → ScTm 0 t → ScTy 0 B → fvTmTy t B ≡ []
  fvTmTy-0 {t} {B} p q rewrite fv0-tm t p | fv0-ty B q = refl

  closed-var : ∀ {t i} → ScTm 0 t → t ≡ var i → ⊥
  closed-var {i = i} p refl = closed-not-var {i} p

obj-var : ∀ {Γ i} → Obj Γ (var i) → lookup Γ i ≡ just ⋆
obj-var (_ , refl , e) = e

-- Every object of Γ is sent to an object of Θ.
AllObj : Ctx → Sub → Ctx → Set
AllObj Θ τ Γ = ∀ o → lookup Γ o ≡ just ⋆ → Obj Θ (lookupₛ τ o)

private
  ext-all : ∀ {Θ Γ A B τ₀ ty tf} → lenₛ τ₀ ≡ len Γ → AllObj Θ τ₀ Γ →
            (A ≡ ⋆ → Obj Θ ty) → (B ≡ ⋆ → ⊥) → AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ A ▸ B)
  ext-all {Θ} {Γ} {A} {B} {τ₀} {ty} {tf} l all hA hB o eo rewrite l with o ==ℕ suc (len Γ)
  ... | true  = ⊥-elim (hB (just-inj eo))
  ... | false with o ==ℕ len Γ
  ...   | true  = hA (just-inj eo)
  ...   | false = all o eo

module _ (closed : Closed) where

  mutual
    -- The base of a term's type in a pasting context is either a pair
    -- of objects, or the term and its type are closed.
    dich : ∀ {Θ s A a b} → Θ ⊢ps → Θ ⊢tm s ∶ A → Base A a b →
           (Obj Θ a × Obj Θ b) ⊎ (ScTm 0 s × ScTy 0 A)
    dich {Θ} (ps d) (var-wf {i} w eq) r =
      let (_ , I , P) = ps-facts d in inj₁ (base-obj {Θ} {i} I P eq r)
    dich P (cst-wf {k} _ _) r = inj₂ (tt , closed k)
    dich {Θ} P (coh-wf {Θ″} {B} {t′} {u′} {τ} p″ w″ a″ ok″ s″) r
      with Base-inv (arr B t′ u′) τ r
    ... | (a′ , b′ , r′ , refl , refl) with bv p″ a″ ok″ r′ | conn′ p″ s″ P
    ...   | ((x′ , refl , ex′) , (y′ , refl , ey′)) | inj₁ all = inj₁ (all x′ ex′ , all y′ ey′)
    ...   | _ | inj₂ cl = inj₂ (cl , sc-ty[] (arr B t′ u′) τ scA cl)
      where
      scA : ScTy (lenₛ τ) (arr B t′ u′)
      scA = subst (λ n → ScTy n (arr B t′ u′)) (sym (snd (sub-sc closed s″))) (ty-sc closed a″)

    -- In a coh's own pasting context, the base of its type is a pair of
    -- objects: otherwise one side would mention no variable.
    bv : ∀ {Θ B t u a b} → Θ ⊢ps → Θ ⊢ty arr B t u → T (cattSide Θ B t u) →
         Base (arr B t u) a b → Obj Θ a × Obj Θ b
    bv {Θ} {.⋆} {t} {u} P (arr-wf dt du) ok base1 = star-obj (star-inv dt) , star-obj′ (star-inv du)
      where
      star-obj : Obj Θ t ⊎ (Σ K λ k → t ≡ cst k) → Obj Θ t
      star-obj (inj₁ o)        = o
      star-obj (inj₂ (k , refl)) = ⊥-elim (side-t-empty {Θ} {⋆} {cst k} {u} P refl ok)
      star-obj′ : Obj Θ u ⊎ (Σ K λ k → u ≡ cst k) → Obj Θ u
      star-obj′ (inj₁ o)        = o
      star-obj′ (inj₂ (k , refl)) = ⊥-elim (side-u-empty {Θ} {⋆} {t} {cst k} P refl ok)
    bv {Θ} {B} {t} {u} P (arr-wf dt du) ok (base+ r) with dich P dt r
    ... | inj₁ o            = o
    ... | inj₂ (sct , scB) = ⊥-elim (side-t-empty {Θ} {B} {t} {u} P (fvTmTy-0 {t} {B} sct scB) ok)

    conn′ : ∀ {Θ Γ τ} → Γ ⊢ps → Θ ⊢sub τ ∶ Γ → Θ ⊢ps → AllObj Θ τ Γ ⊎ ScSub 0 τ
    conn′ (ps d) s P = conn d s P

    -- A substitution out of a pasting context sends all objects to
    -- objects, or is closed: pasting contexts are connected.
    conn : ∀ {Θ Γ x A τ} → Γ ⊢ps x ∶ A → Θ ⊢sub τ ∶ Γ → Θ ⊢ps → AllObj Θ τ Γ ⊎ ScSub 0 τ
    conn {Θ} pss (,-wf {t = t₀} (⟨⟩-wf _) d₀) P with star-inv d₀
    ... | inj₁ ob       = inj₁ (all₀ ob)
      where
      all₀ : Obj Θ t₀ → AllObj Θ (⟨⟩ ,ₛ t₀) (ε ▸ ⋆)
      all₀ ob o eo with o ==ℕ 0
      ... | true  = ob
      all₀ ob o () | false
    ... | inj₂ (k , refl) = inj₂ (tt , tt)
    conn (psd d) s P = conn d s P
    conn (pse d) (,-wf (,-wf s₀ dy) df) P = conn-pse d s₀ dy df P (conn d s₀ P) (PsTy-base (ps-ty d))

    conn-pse : ∀ {Θ Γ x A τ₀ ty tf} (d : Γ ⊢ps x ∶ A) (s₀ : Θ ⊢sub τ₀ ∶ Γ)
               (dy : Θ ⊢tm ty ∶ A [ τ₀ ]ty)
               (df : Θ ⊢tm tf ∶ arr A (var x) (var (len Γ)) [ τ₀ ,ₛ ty ]ty) → Θ ⊢ps →
               AllObj Θ τ₀ Γ ⊎ ScSub 0 τ₀ →
               (A ≡ ⋆) ⊎ (Σ Nat λ i → Σ Nat λ j → Base A (var i) (var j)) →
               AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
                 ⊎ ScSub 0 (τ₀ ,ₛ ty ,ₛ tf)
    conn-pse {Θ} {Γ} {x} {.⋆} {τ₀} {ty} {tf} d s₀ dy df P IH (inj₁ refl) = go IH (dich P df base1)
      where
      l : lenₛ τ₀ ≡ len Γ
      l = snd (sub-sc closed s₀)
      x<′ : T (x <ℕ lenₛ τ₀)
      x<′ = subst (λ m → T (x <ℕ m)) (sym l) (ps-scope d)
      ex : lookup Γ x ≡ just ⋆
      ex = fst (ps-facts d)
      X Y : Tm
      X = lookupₛ (τ₀ ,ₛ ty) x
      Y = lookupₛ (τ₀ ,ₛ ty) (len Γ)
      eX : X ≡ lookupₛ τ₀ x
      eX = lookupₛ-wk τ₀ ty x x<′
      eY : Y ≡ ty
      eY = trans (cong (lookupₛ (τ₀ ,ₛ ty)) (sym l)) (lookupₛ-top τ₀ ty)
      go : AllObj Θ τ₀ Γ ⊎ ScSub 0 τ₀ → (Obj Θ X × Obj Θ Y) ⊎ (ScTm 0 tf × ScTy 0 (arr ⋆ X Y)) →
           AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ)))
             ⊎ ScSub 0 (τ₀ ,ₛ ty ,ₛ tf)
      go (inj₁ all) (inj₁ (_ , oY)) =
        inj₁ (ext-all {Θ} {Γ} {⋆} {arr ⋆ (var x) (var (len Γ))} {τ₀} {ty} {tf} l all
                (λ _ → subst (Obj Θ) eY oY) (λ ()))
      go (inj₁ all) (inj₂ (_ , (_ , scX , _))) =
        let (k , ek , _) = all x ex in ⊥-elim (closed-var (subst (ScTm 0) eX scX) ek)
      go (inj₂ cl₀) (inj₁ ((k , ek , _) , _)) =
        ⊥-elim (closed-var (sc-lookup τ₀ x x<′ cl₀) (trans (sym eX) ek))
      go (inj₂ cl₀) (inj₂ (sctf , (_ , _ , scY))) = inj₂ ((cl₀ , subst (ScTm 0) eY scY) , sctf)
    conn-pse {Θ} {Γ} {x} {A} {τ₀} {ty} {tf} d s₀ dy df P IH (inj₂ (i , j , rA)) =
      go IH (dich P dy (Base-[] τ₀ rA)) (dich P df (Base-[] (τ₀ ,ₛ ty) (base+ {t = var x} {u = var (len Γ)} rA)))
      where
      l : lenₛ τ₀ ≡ len Γ
      l = snd (sub-sc closed s₀)
      ei : lookup Γ i ≡ just ⋆
      ei = let (_ , I , P′) = ps-facts d in obj-var {Γ} {i} (fst (base-obj {Γ} {x} I P′ (fst (ps-facts d)) rA))
      i< : T (i <ℕ lenₛ τ₀)
      i< = subst (λ m → T (i <ℕ m)) (sym l) (lookup-< Γ i ei)
      go : AllObj Θ τ₀ Γ ⊎ ScSub 0 τ₀ →
           (Obj Θ (lookupₛ τ₀ i) × Obj Θ (lookupₛ τ₀ j)) ⊎ (ScTm 0 ty × ScTy 0 (A [ τ₀ ]ty)) →
           (Obj Θ (lookupₛ (τ₀ ,ₛ ty) i) × Obj Θ (lookupₛ (τ₀ ,ₛ ty) j))
             ⊎ (ScTm 0 tf × ScTy 0 (arr A (var x) (var (len Γ)) [ τ₀ ,ₛ ty ]ty)) →
           AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ A ▸ arr A (var x) (var (len Γ)))
             ⊎ ScSub 0 (τ₀ ,ₛ ty ,ₛ tf)
      go (inj₁ all) _ _ =
        inj₁ (ext-all {Θ} {Γ} {A} {arr A (var x) (var (len Γ))} {τ₀} {ty} {tf} l all
                (λ e → ⊥-elim (base-not-⋆ rA e)) (λ ()))
      go (inj₂ cl₀) (inj₁ ((k , ek , _) , _)) _ = ⊥-elim (closed-var (sc-lookup τ₀ i i< cl₀) ek)
      go (inj₂ cl₀) (inj₂ _) (inj₁ ((k , ek , _) , _)) =
        ⊥-elim (closed-var (sc-lookup τ₀ i i< cl₀) (trans (sym (lookupₛ-wk τ₀ ty i i<)) ek))
      go (inj₂ cl₀) (inj₂ (scty , _)) (inj₂ (sctf , _)) = inj₂ ((cl₀ , scty) , sctf)

------------------------------------------------------------------------
-- Groups.

record Group : Set₁ where
  infixl 7 _·_
  infix  8 _⁻¹
  field
    G     : Set
    _·_   : G → G → G
    e     : G
    _⁻¹   : G → G
    assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
    idˡ   : ∀ a → e · a ≡ a
    idʳ   : ∀ a → a · e ≡ a
    invˡ  : ∀ a → a ⁻¹ · a ≡ e
    invʳ  : ∀ a → a · a ⁻¹ ≡ e

  -- a⁻¹ · (a · b) = b
  cancelˡ : ∀ a b → a ⁻¹ · (a · b) ≡ b
  cancelˡ a b = trans (sym (assoc (a ⁻¹) a b)) (trans (cong (_· b) (invˡ a)) (idˡ b))

  -- (a⁻¹ · b) · (b⁻¹ · c) = a⁻¹ · c
  telescope : ∀ a b c → (a ⁻¹ · b) · (b ⁻¹ · c) ≡ a ⁻¹ · c
  telescope a b c =
    trans (assoc (a ⁻¹) b (b ⁻¹ · c))
      (cong (a ⁻¹ ·_) (trans (sym (assoc b (b ⁻¹) c)) (trans (cong (_· c) (invʳ b)) (idˡ c))))

  -- (a⁻¹ · b)⁻¹ · (a⁻¹ · c) = b⁻¹ · c
  relative : ∀ a b c → (a ⁻¹ · b) ⁻¹ · (a ⁻¹ · c) ≡ b ⁻¹ · c
  relative a b c =
    trans (cong ((a ⁻¹ · b) ⁻¹ ·_) (sym (telescope a b c))) (cancelˡ (a ⁻¹ · b) (b ⁻¹ · c))

------------------------------------------------------------------------
-- The model B G.

module Model (closed : Closed) (𝔾 : Group) (M : K → Group.G 𝔾) where

  open Group 𝔾

  Env : Set
  Env = Nat → G

  -- Values of a substitution, in the same order.
  infixl 5 _▹_
  data VS : Set where
    []  : VS
    _▹_ : VS → G → VS

  lenV : VS → Nat
  lenV []       = 0
  lenV (vs ▹ _) = suc (lenV vs)

  lookupV : VS → Env
  lookupV []       i = e
  lookupV (vs ▹ g) i = if i ==ℕ lenV vs then g else lookupV vs i

  -- Potentials of the objects of a pasting context.
  private
    step? : Ty → Ty → Maybe Nat
    step? ⋆ (arr ⋆ (var x) (var n)) = just x
    step? _ _                       = nothing

    stepWith : Maybe Nat → Nat → G → (Nat → G) → Nat → G
    stepWith (just x) n w P i = if i ==ℕ n then P x · w else P i
    stepWith nothing  n w P i = P i

  pot : Ctx → Env → Nat → G
  pot (Γ ▸ A ▸ B) η = stepWith (step? A B) (len Γ) (η (suc (len Γ))) (pot Γ η)
  pot _           η = λ _ → e

  -- A 1-dimensional coherence x → y over Θ is the composite along Θ.
  cohVal : Ctx → Ty → Env → G
  cohVal Θ (arr ⋆ (var a) (var b)) η = pot Θ η a ⁻¹ · pot Θ η b
  cohVal Θ _                       η = e

  mutual
    ⟦_⟧ : Tm → Env → G
    ⟦ var i ⟧     ρ = ρ i
    ⟦ coh Θ A τ ⟧ ρ = cohVal Θ A (lookupV (⟦ τ ⟧s ρ))
    ⟦ cst k ⟧     ρ = M k

    ⟦_⟧s : Sub → Env → VS
    ⟦ ⟨⟩ ⟧s     ρ = []
    ⟦ σ ,ₛ t ⟧s ρ = ⟦ σ ⟧s ρ ▹ ⟦ t ⟧ ρ

  -- Inhabitation of a type in B G.
  Holds : Ty → Env → Set
  Holds (arr (arr ⋆ _ _) f g) ρ = ⟦ f ⟧ ρ ≡ ⟦ g ⟧ ρ
  Holds _                     ρ = ⊤

  ValidEnv : Ctx → Env → Set
  ValidEnv Γ ρ = ∀ i A → lookup Γ i ≡ just A → Holds A ρ

  ----------------------------------------------------------------------
  -- Environments.

  Agree : Nat → Env → Env → Set
  Agree n η η′ = ∀ i → T (i <ℕ n) → η i ≡ η′ i

  mutual
    env-tm : ∀ {n η η′} t → ScTm n t → Agree n η η′ → ⟦ t ⟧ η ≡ ⟦ t ⟧ η′
    env-tm (var i)     p a = a i p
    env-tm (coh Θ A τ) p a = cong (λ vs → cohVal Θ A (lookupV vs)) (env-sub τ p a)
    env-tm (cst k)     _ _ = refl

    env-sub : ∀ {n η η′} σ → ScSub n σ → Agree n η η′ → ⟦ σ ⟧s η ≡ ⟦ σ ⟧s η′
    env-sub ⟨⟩       _       _ = refl
    env-sub (σ ,ₛ t) (p , q) a = cong₂ _▹_ (env-sub σ p a) (env-tm t q a)

  Holds-ext : ∀ {n η η′} A → ScTy n A → Agree n η η′ → Holds A η → Holds A η′
  Holds-ext ⋆                       _               _ h = h
  Holds-ext (arr ⋆ _ _)             _               _ h = h
  Holds-ext (arr (arr ⋆ _ _) f g)   (_ , pf , pg)   a h =
    trans (sym (env-tm f pf a)) (trans h (env-tm g pg a))
  Holds-ext (arr (arr (arr _ _ _) _ _) _ _) _       _ h = h

  lenV-⟦⟧ : ∀ σ ρ → lenV (⟦ σ ⟧s ρ) ≡ lenₛ σ
  lenV-⟦⟧ ⟨⟩       ρ = refl
  lenV-⟦⟧ (σ ,ₛ t) ρ = cong suc (lenV-⟦⟧ σ ρ)

  lookupV-wk : ∀ vs g → Agree (lenV vs) (lookupV vs) (lookupV (vs ▹ g))
  lookupV-wk vs g i p rewrite <→≢ i (lenV vs) p = refl

  lookupV-top : ∀ vs g → lookupV (vs ▹ g) (lenV vs) ≡ g
  lookupV-top vs g rewrite ==-refl (lenV vs) = refl

  lookupV-⟦⟧ : ∀ σ ρ i → T (i <ℕ lenₛ σ) → lookupV (⟦ σ ⟧s ρ) i ≡ ⟦ lookupₛ σ i ⟧ ρ
  lookupV-⟦⟧ (σ ,ₛ t) ρ i p rewrite lenV-⟦⟧ σ ρ with i ==ℕ lenₛ σ in eq
  ... | true  = refl
  ... | false = lookupV-⟦⟧ σ ρ i (<suc-≢ i (lenₛ σ) p eq)

  ----------------------------------------------------------------------
  -- Semantic substitution.

  mutual
    sem-tm : ∀ t σ ρ → ScTm (lenₛ σ) t → ⟦ t [ σ ]tm ⟧ ρ ≡ ⟦ t ⟧ (lookupV (⟦ σ ⟧s ρ))
    sem-tm (var i)     σ ρ p = sym (lookupV-⟦⟧ σ ρ i p)
    sem-tm (coh Θ A τ) σ ρ p = cong (λ vs → cohVal Θ A (lookupV vs)) (sem-sub τ σ ρ p)
    sem-tm (cst k)     σ ρ _ = refl

    sem-sub : ∀ τ σ ρ → ScSub (lenₛ σ) τ → ⟦ τ ∘ σ ⟧s ρ ≡ ⟦ τ ⟧s (lookupV (⟦ σ ⟧s ρ))
    sem-sub ⟨⟩       σ ρ _       = refl
    sem-sub (τ ,ₛ t) σ ρ (p , q) = cong₂ _▹_ (sem-sub τ σ ρ p) (sem-tm t σ ρ q)

  Holds-sub : ∀ A σ ρ → ScTy (lenₛ σ) A → Holds (A [ σ ]ty) ρ → Holds A (lookupV (⟦ σ ⟧s ρ))
  Holds-sub ⋆                     σ ρ _ h = h
  Holds-sub (arr ⋆ _ _)           σ ρ _ h = h
  Holds-sub (arr (arr ⋆ _ _) f g) σ ρ (_ , pf , pg) h =
    trans (sym (sem-tm f σ ρ pf)) (trans h (sem-tm g σ ρ pg))
  Holds-sub (arr (arr (arr _ _ _) _ _) _ _) σ ρ _ h = h

  ----------------------------------------------------------------------
  -- Potentials.

  pot-ext : ∀ Γ {η η′} → Agree (len Γ) η η′ → ∀ o → pot Γ η o ≡ pot Γ η′ o
  pot-ext ε           a o = refl
  pot-ext (ε ▸ A)     a o = refl
  pot-ext (Γ ▸ A ▸ B) {η} {η′} a o
    rewrite a (suc (len Γ)) (<-suc-self (suc (len Γ))) with step? A B
  ... | nothing = pot-ext Γ (λ i p → a i (<-suc i _ (<-suc i _ p))) o
  ... | just x with o ==ℕ len Γ
  ...   | true  = cong (_· η′ (suc (len Γ))) (pot-ext Γ (λ i p → a i (<-suc i _ (<-suc i _ p))) x)
  ...   | false = pot-ext Γ (λ i p → a i (<-suc i _ (<-suc i _ p))) o

  private
    arr-dom : ∀ {X Y Z P Q R} → arr X Y Z ≡ arr P Q R → X ≡ P
    arr-dom refl = refl

    arr⋆≢ : ∀ {X Y Z Q R Q′ R′} → arr (arr X Y Z) Q R ≡ arr ⋆ Q′ R′ → ⊥
    arr⋆≢ ()

  -- In a pasting context with a valid environment, every 1-cell
  -- variable x → y has value pot(x)⁻¹ · pot(y).
  mutual
    pot-var : ∀ {Θ z C η f i j} → Θ ⊢ps z ∶ C → ValidEnv Θ η →
              lookup Θ f ≡ just (arr ⋆ (var i) (var j)) → η f ≡ pot Θ η i ⁻¹ · pot Θ η j
    pot-var {f = f} pss V eq with f ==ℕ 0
    pot-var pss V () | true
    pot-var pss V () | false
    pot-var (psd d) V eq = pot-var d V eq
    pot-var (pse d) V eq = pot-var-pse d V eq (PsTy-base (ps-ty d))

    pot-var-pse : ∀ {Γ x A η f i j} (d : Γ ⊢ps x ∶ A) →
                  ValidEnv (Γ ▸ A ▸ arr A (var x) (var (len Γ))) η →
                  lookup (Γ ▸ A ▸ arr A (var x) (var (len Γ))) f ≡ just (arr ⋆ (var i) (var j)) →
                  (A ≡ ⋆) ⊎ (Σ Nat λ k → Σ Nat λ l → Base A (var k) (var l)) →
                  η f ≡ pot (Γ ▸ A ▸ arr A (var x) (var (len Γ))) η i ⁻¹
                        · pot (Γ ▸ A ▸ arr A (var x) (var (len Γ))) η j
    pot-var-pse {Γ} {x} {.⋆} {η} {f} {i} {j} d V eq (inj₁ refl) with f ==ℕ suc (len Γ) in e₁
    ... | true  = subst (λ g → η g ≡ _) (sym (==→≡ f (suc (len Γ)) e₁)) (top i j (just-inj eq))
      where
      n = len Γ
      x< : T (x <ℕ n)
      x< = lookup-< Γ x (fst (ps-facts d))
      top : ∀ i j → arr ⋆ (var x) (var n) ≡ arr ⋆ (var i) (var j) →
            η (suc n) ≡ pot (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var n)) η i ⁻¹
                        · pot (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var n)) η j
      top .x .n refl rewrite <→≢ x n x< | ==-refl n = sym (cancelˡ (pot Γ η x) (η (suc n)))
    ... | false with f ==ℕ len Γ
    ...   | true  = ⊥-elim (⋆≢arr eq)
    ...   | false = rest (fst (snd (ps-facts d)) f ⋆ i j eq)
      where
      n = len Γ
      V₀ : ValidEnv Γ η
      V₀ k C e = V k C (lookup-wk′ (Γ ▸ ⋆) k _ (lookup-wk′ Γ k ⋆ e))
      rest : (lookup Γ i ≡ just ⋆) × (lookup Γ j ≡ just ⋆) →
             η f ≡ pot (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var n)) η i ⁻¹
                   · pot (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var n)) η j
      rest (ei , ej) rewrite <→≢ i n (lookup-< Γ i ei) | <→≢ j n (lookup-< Γ j ej) = pot-var d V₀ eq
    pot-var-pse {Γ} {x} {arr ⋆ (var k) (var l)} {η} {f} {i} {j} d V eq (inj₂ (k , l , base1))
      with f ==ℕ suc (len Γ)
    ... | true  = ⊥-elim (arr⋆≢ (just-inj eq))
    ... | false with f ==ℕ len Γ in e₂
    ...   | true  = mid i j (just-inj eq)
      where
      n = len Γ
      hold : η x ≡ η n
      hold = V (suc n) _ (lookup-top (Γ ▸ arr ⋆ (var k) (var l)) _)
      V₀ : ValidEnv Γ η
      V₀ k′ C e = V k′ C (lookup-wk′ (Γ ▸ _) k′ _ (lookup-wk′ Γ k′ _ e))
      mid : ∀ i j → arr ⋆ (var k) (var l) ≡ arr ⋆ (var i) (var j) →
            η f ≡ pot Γ η i ⁻¹ · pot Γ η j
      mid .k .l refl rewrite ==→≡ f n e₂ = trans (sym hold) (pot-var d V₀ (fst (ps-facts d)))
    ...   | false = pot-var d V₀ eq
      where
      V₀ : ValidEnv Γ η
      V₀ k′ C e = V k′ C (lookup-wk′ (Γ ▸ _) k′ _ (lookup-wk′ Γ k′ _ e))
    pot-var-pse {Γ} {x} {arr A′ t u} {η} {f} {i} {j} d V eq (inj₂ (k , l , base+ r))
      with f ==ℕ suc (len Γ)
    ... | true  = ⊥-elim (base-not-⋆ (base+ {t = t} {u = u} r) (arr-dom (just-inj eq)))
    ... | false with f ==ℕ len Γ
    ...   | true  = ⊥-elim (base-not-⋆ r (arr-dom (just-inj eq)))
    ...   | false = pot-var d V₀ eq
      where
      V₀ : ValidEnv Γ η
      V₀ k′ C e = V k′ C (lookup-wk′ (Γ ▸ _) k′ _ (lookup-wk′ Γ k′ _ e))

  ----------------------------------------------------------------------
  -- Index bookkeeping for one pse step.

  private
    lkS2 : ∀ {τ₀ a b o n} → lenₛ τ₀ ≡ n → T (o <ℕ n) → lookupₛ (τ₀ ,ₛ a ,ₛ b) o ≡ lookupₛ τ₀ o
    lkS2 {τ₀} {a} {b} {o} refl p =
      trans (lookupₛ-wk (τ₀ ,ₛ a) b o (<-suc o _ p)) (lookupₛ-wk τ₀ a o p)

    lkSn : ∀ {τ₀ a b n} → lenₛ τ₀ ≡ n → lookupₛ (τ₀ ,ₛ a ,ₛ b) n ≡ a
    lkSn {τ₀} {a} {b} refl =
      trans (lookupₛ-wk (τ₀ ,ₛ a) b (lenₛ τ₀) (<-suc-self (lenₛ τ₀))) (lookupₛ-top τ₀ a)

    lk2 : ∀ {Γ A B o} → (B ≡ ⋆ → ⊥) → lookup (Γ ▸ A ▸ B) o ≡ just ⋆ →
          ((o ≡ len Γ) × (A ≡ ⋆)) ⊎ (lookup Γ o ≡ just ⋆)
    lk2 {Γ} {A} {B} {o} hB eq with o ==ℕ suc (len Γ)
    ... | true  = ⊥-elim (hB (just-inj eq))
    ... | false with o ==ℕ len Γ in e
    ...   | true  = inj₁ (==→≡ o (len Γ) e , just-inj eq)
    ...   | false = inj₂ eq

    lV2 : ∀ vs a b → Agree (lenV vs) (lookupV vs) (lookupV (vs ▹ a ▹ b))
    lV2 vs a b i p = trans (lookupV-wk vs a i p) (lookupV-wk (vs ▹ a) b i (<-suc i _ p))

    lVtop : ∀ vs a b → lookupV (vs ▹ a ▹ b) (suc (lenV vs)) ≡ b
    lVtop vs a b = lookupV-top (vs ▹ a) b

    0< : ∀ {x n} → T (x <ℕ n) → T (0 <ℕ n)
    0< {n = suc n} _ = tt

    arr-tm : ∀ {a b c d} → arr ⋆ a b ≡ arr ⋆ c d → (a ≡ c) × (b ≡ d)
    arr-tm refl = refl , refl

  -- Potentials read through τ.
  Qt : Ctx → Env → Tm → G
  Qt Θ η (var i) = pot Θ η i
  Qt Θ η _       = e

  ----------------------------------------------------------------------
  -- Value of 1-cell terms in a pasting context (1-dimensional
  -- contractibility of pasting contexts in B G).

  mutual
    val : ∀ {Θ η s T′ i j} → Θ ⊢ps → ValidEnv Θ η →
          Θ ⊢tm s ∶ T′ → T′ ≡ arr ⋆ (var i) (var j) →
          ⟦ s ⟧ η ≡ pot Θ η i ⁻¹ · pot Θ η j
    val (ps dΘ) V (var-wf w eq) refl = pot-var dΘ V eq
    val {i = i} dΘ V (cst-wf {k} _ _) e =
      ⊥-elim (closed-not-var {i} (fst (snd (subst (ScTy 0) e (closed k)))))
    val dΘ V (coh-wf {A = arr _ _ _} _ _ _ _ _) e = ⊥-elim (arr⋆≢ e)
    val {Θ} {η = η} {i = i} {j} dΘ V (coh-wf {Θ″} {⋆} {t′} {u′} {τ} p″ w″ a″ ok″ s″) e
      with bv closed p″ a″ ok″ base1
    ... | ((x′ , refl , ex′) , (y′ , refl , ey′)) with conn′ closed p″ s″ dΘ
    ...   | inj₂ cl = ⊥-elim (closed-var (sc-lookup τ x′ x<τ cl) (fst (arr-tm e)))
      where
      x<τ : T (x′ <ℕ lenₛ τ)
      x<τ = subst (λ m → T (x′ <ℕ m)) (sym (snd (sub-sc closed s″))) (lookup-< Θ″ x′ ex′)
    ...   | inj₁ all = goal p″
      where
      Q0 = Qt Θ η (lookupₛ τ 0)
      goal : Θ″ ⊢ps → pot Θ″ (lookupV (⟦ τ ⟧s η)) x′ ⁻¹ · pot Θ″ (lookupV (⟦ τ ⟧s η)) y′
                      ≡ pot Θ η i ⁻¹ · pot Θ η j
      goal (ps d″)
        rewrite potT dΘ V d″ s″ all x′ ex′ | potT dΘ V d″ s″ all y′ ey′
              | fst (arr-tm e) | snd (arr-tm e) = relative Q0 (pot Θ η i) (pot Θ η j)

    potT : ∀ {Θ η Γ x A τ} → Θ ⊢ps → ValidEnv Θ η →
           Γ ⊢ps x ∶ A → Θ ⊢sub τ ∶ Γ → AllObj Θ τ Γ →
           ∀ o → lookup Γ o ≡ just ⋆ →
           pot Γ (lookupV (⟦ τ ⟧s η)) o ≡ Qt Θ η (lookupₛ τ 0) ⁻¹ · Qt Θ η (lookupₛ τ o)
    potT {Θ} {η = η} dΘ V pss (,-wf {t = t₀} (⟨⟩-wf _) d₀) all o eo with o ==ℕ 0 in e₀
    ... | true  = sym (invˡ (Qt Θ η t₀))
    potT dΘ V pss (,-wf (⟨⟩-wf _) d₀) all o () | false
    potT dΘ V (psd d) s all = potT dΘ V d s all
    potT dΘ V (pse d) (,-wf (,-wf s₀ dy) df) all =
      potT-pse dΘ V d s₀ dy df all (PsTy-base (ps-ty d))

    potT-pse : ∀ {Θ η Γ x A τ₀ ty tf} → Θ ⊢ps → ValidEnv Θ η →
               (d : Γ ⊢ps x ∶ A) (s₀ : Θ ⊢sub τ₀ ∶ Γ)
               (dy : Θ ⊢tm ty ∶ A [ τ₀ ]ty)
               (df : Θ ⊢tm tf ∶ arr A (var x) (var (len Γ)) [ τ₀ ,ₛ ty ]ty) →
               AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ A ▸ arr A (var x) (var (len Γ))) →
               (A ≡ ⋆) ⊎ (Σ Nat λ k → Σ Nat λ l → Base A (var k) (var l)) →
               ∀ o → lookup (Γ ▸ A ▸ arr A (var x) (var (len Γ))) o ≡ just ⋆ →
               pot (Γ ▸ A ▸ arr A (var x) (var (len Γ))) (lookupV (⟦ τ₀ ,ₛ ty ,ₛ tf ⟧s η)) o
                 ≡ Qt Θ η (lookupₛ (τ₀ ,ₛ ty ,ₛ tf) 0) ⁻¹ · Qt Θ η (lookupₛ (τ₀ ,ₛ ty ,ₛ tf) o)
    potT-pse {Θ} {η = η} {Γ} {x} {.⋆} {τ₀} {ty} {tf} dΘ V d s₀ dy df all (inj₁ refl) o eo
      with lk2 {Γ} {⋆} {arr ⋆ (var x) (var (len Γ))} {o} (λ ()) eo
    ... | inj₁ (refl , _) =
      -- the newly attached object n, with arrow f : x → n
      trans (cong (λ b → (if len Γ ==ℕ len Γ then pot Γ η″ x · b else pot Γ η″ (len Γ))) top)
        (trans (cong (λ b → if b then pot Γ η″ x · ⟦ tf ⟧ η else pot Γ η″ (len Γ)) (==-refl (len Γ)))
          (trans (cong (_· ⟦ tf ⟧ η) (trans (pot-ext Γ agree x) (IH x ex)))
            (trans (cong ((Q0′ ⁻¹ · Qx) ·_) vf)
              (trans (telescope Q0′ Qx (Qt Θ η (var kn)))
                (cong₂ (λ a b → Qt Θ η a ⁻¹ · Qt Θ η b) (sym e0) (sym ekn))))))
      where
      n = len Γ
      η₀ = lookupV (⟦ τ₀ ⟧s η)
      η″ = lookupV (⟦ τ₀ ,ₛ ty ,ₛ tf ⟧s η)
      l : lenₛ τ₀ ≡ n
      l = snd (sub-sc closed s₀)
      lV : lenV (⟦ τ₀ ⟧s η) ≡ n
      lV = trans (lenV-⟦⟧ τ₀ η) l
      ex : lookup Γ x ≡ just ⋆
      ex = fst (ps-facts d)
      x< : T (x <ℕ n)
      x< = lookup-< Γ x ex
      agree : Agree n η″ η₀
      agree i p = sym (lV2 (⟦ τ₀ ⟧s η) (⟦ ty ⟧ η) (⟦ tf ⟧ η) i (subst (λ m → T (i <ℕ m)) (sym lV) p))
      top : η″ (suc n) ≡ ⟦ tf ⟧ η
      top = trans (cong (λ m → η″ (suc m)) (sym lV)) (lVtop (⟦ τ₀ ⟧s η) (⟦ ty ⟧ η) (⟦ tf ⟧ η))
      all₀ : AllObj Θ τ₀ Γ
      all₀ k ek = subst (Obj Θ) (lkS2 {τ₀} {ty} {tf} l (lookup-< Γ k ek))
                    (all k (lookup-wk′ (Γ ▸ ⋆) k _ (lookup-wk′ Γ k ⋆ ek)))
      IH : ∀ o → lookup Γ o ≡ just ⋆ → pot Γ η₀ o ≡ Qt Θ η (lookupₛ τ₀ 0) ⁻¹ · Qt Θ η (lookupₛ τ₀ o)
      IH = potT dΘ V d s₀ all₀
      Q0′ = Qt Θ η (lookupₛ τ₀ 0)
      e0 : lookupₛ (τ₀ ,ₛ ty ,ₛ tf) 0 ≡ lookupₛ τ₀ 0
      e0 = lkS2 {τ₀} {ty} {tf} l (0< {x} {n} x<)
      Qx = Qt Θ η (lookupₛ τ₀ x)
      -- the images of x and n are variables
      okx = all₀ x ex
      kx = fst okx
      ekx : lookupₛ τ₀ x ≡ var kx
      ekx = fst (snd okx)
      okn = all n (trans (lookup-wk {Γ ▸ ⋆} {n} _ (<-suc-self n)) (lookup-top Γ ⋆))
      kn = fst okn
      ekn : lookupₛ (τ₀ ,ₛ ty ,ₛ tf) n ≡ var kn
      ekn = fst (snd okn)
      eX : lookupₛ (τ₀ ,ₛ ty) x ≡ var kx
      eX = trans (lookupₛ-wk τ₀ ty x (subst (λ m → T (x <ℕ m)) (sym l) x<)) ekx
      eY : lookupₛ (τ₀ ,ₛ ty) n ≡ var kn
      eY = trans (trans (cong (lookupₛ (τ₀ ,ₛ ty)) (sym l)) (lookupₛ-top τ₀ ty))
                 (trans (sym (lkSn {τ₀} {ty} {tf} l)) ekn)
      vf : ⟦ tf ⟧ η ≡ Qx ⁻¹ · Qt Θ η (var kn)
      vf = trans (val dΘ V df (cong₂ (arr ⋆) eX eY))
                 (cong (λ t → Qt Θ η t ⁻¹ · pot Θ η kn) (sym ekx))
    ... | inj₂ eo′ rewrite <→≢ o (len Γ) (lookup-< Γ o eo′) = potT-old dΘ V d s₀ all o eo′
    potT-pse {Γ = Γ} {x} {arr ⋆ (var k) (var l)} dΘ V d s₀ dy df all (inj₂ (k , l , base1)) o eo
      with lk2 {Γ} {arr ⋆ (var k) (var l)} {arr (arr ⋆ (var k) (var l)) (var x) (var (len Γ))} {o} (λ ()) eo
    ... | inj₁ (_ , ())
    ... | inj₂ eo′ = potT-old dΘ V d s₀ all o eo′
    potT-pse {Γ = Γ} {x} {arr A′ t u} dΘ V d s₀ dy df all (inj₂ (k , l , base+ r)) o eo
      with lk2 {Γ} {arr A′ t u} {arr (arr A′ t u) (var x) (var (len Γ))} {o} (λ ()) eo
    ... | inj₁ (_ , ())
    ... | inj₂ eo′ = potT-old dΘ V d s₀ all o eo′

    -- Objects that were already there.
    potT-old : ∀ {Θ η Γ x A B τ₀ ty tf} → Θ ⊢ps → ValidEnv Θ η →
               (d : Γ ⊢ps x ∶ A) (s₀ : Θ ⊢sub τ₀ ∶ Γ) →
               AllObj Θ (τ₀ ,ₛ ty ,ₛ tf) (Γ ▸ A ▸ B) →
               ∀ o → lookup Γ o ≡ just ⋆ →
               pot Γ (lookupV (⟦ τ₀ ,ₛ ty ,ₛ tf ⟧s η)) o
                 ≡ Qt Θ η (lookupₛ (τ₀ ,ₛ ty ,ₛ tf) 0) ⁻¹ · Qt Θ η (lookupₛ (τ₀ ,ₛ ty ,ₛ tf) o)
    potT-old {Θ} {η} {Γ} {x} {A} {B} {τ₀} {ty} {tf} dΘ V d s₀ all o eo =
      trans (pot-ext Γ agree o)
        (trans (potT dΘ V d s₀ all₀ o eo)
          (cong₂ (λ a b → Qt Θ η a ⁻¹ · Qt Θ η b) (sym e0) (sym (lkS2 {τ₀} {ty} {tf} l o<))))
      where
      n = len Γ
      l : lenₛ τ₀ ≡ n
      l = snd (sub-sc closed s₀)
      lV : lenV (⟦ τ₀ ⟧s η) ≡ n
      lV = trans (lenV-⟦⟧ τ₀ η) l
      agree : Agree n (lookupV (⟦ τ₀ ,ₛ ty ,ₛ tf ⟧s η)) (lookupV (⟦ τ₀ ⟧s η))
      agree i p = sym (lV2 (⟦ τ₀ ⟧s η) (⟦ ty ⟧ η) (⟦ tf ⟧ η) i (subst (λ m → T (i <ℕ m)) (sym lV) p))
      o< : T (o <ℕ n)
      o< = lookup-< Γ o eo
      e0 : lookupₛ (τ₀ ,ₛ ty ,ₛ tf) 0 ≡ lookupₛ τ₀ 0
      e0 = lkS2 {τ₀} {ty} {tf} l (0< {o} {n} o<)
      all₀ : AllObj Θ τ₀ Γ
      all₀ k ek = subst (Obj Θ) (lkS2 {τ₀} {ty} {tf} l (lookup-< Γ k ek))
                    (all k (lookup-wk′ (Γ ▸ A) k B (lookup-wk′ Γ k A ek)))
