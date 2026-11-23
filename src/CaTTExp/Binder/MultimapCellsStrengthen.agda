------------------------------------------------------------------------
-- Strengthening onto a canonical support (ledger S26j, step 2b): if
-- infer Φ u = A, then the canonical head of u types its own term at
-- the renamed type:
--
--   infer Φ′ (u[ren]) ≡ just (A[ren])
--
-- where Φ′ and u[ren] are the context and term of `canon k Φ u` and
-- ren = renOf (supAtoms k Φ u) (supVars Φ u). The argument: u uses only
-- entries of its support or no entry at all (`vars-sup`, `lookup-none`), so by `infer-agree` it has the
-- same type in Φ with every other entry blanked to the type of pt;
-- ren is a well-typed substitution from that context to Φ′; then
-- `Subst.sub-infer`. Neither well-formedness of Φ nor closure of the
-- support under dependencies is needed here.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsStrengthen where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Subst using (_⊢_∶_; ⊢in; sub-infer)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.Multimap using (mctx; mterm)

------------------------------------------------------------------------
-- Booleans and lists of naturals.

T-if : ∀ {A : Set} b {x y : A} → T b → (if b then x else y) ≡ x
T-if true _ = refl

F-if : ∀ {A : Set} b {x y : A} → (T b → ⊥) → (if b then x else y) ≡ y
F-if true  n = ⊥-elim (n tt)
F-if false n = refl

data _⊎′_ (A B : Set) : Set where
  inl : A → A ⊎′ B
  inr : B → A ⊎′ B

dec : ∀ b → T b ⊎′ (T b → ⊥)
dec true  = inl tt
dec false = inr (λ ())

closeFrom-mono : ∀ Φ j S i → T (elem i S) → T (elem i (closeFrom Φ j S))
closeFrom-mono Φ zero    S i p = p
closeFrom-mono Φ (suc j) S i p with dec (elem j S)
... | inl q = closeFrom-mono Φ j _ i
                (subst T (sym (cong (elem i) (T-if (elem j S) q))) (elem-++l i S (varsY (nthY Φ j)) p))
... | inr q = closeFrom-mono Φ j _ i (subst T (sym (cong (elem i) (F-if (elem j S) q))) p)

upTo-elem : ∀ n i → T (i <ℕ n) → T (elem i (upTo n))
upTo-elem (suc n) i p with dec (i <ℕ n)
... | inl q = elem-++l i (upTo n) (n ∷ []) (upTo-elem n i q)
... | inr q = elem-++r i (upTo n) (n ∷ []) (∨-l (i ==ℕ n) false (last i n p q))
  where
  last : ∀ i n → T (i <ℕ suc n) → (T (i <ℕ n) → ⊥) → T (i ==ℕ n)
  last zero    zero    _ _ = tt
  last zero    (suc n) _ q = ⊥-elim (q tt)
  last (suc i) zero    p _ = ⊥-elim (lt0 i p)
    where
    lt0 : ∀ i → T (i <ℕ 0) → ⊥
    lt0 i ()
  last (suc i) (suc n) p q = last i n p q

filter-elem : ∀ (p : Nat → Bool) xs i → T (p i) → T (elem i xs) → T (elem i (filter p xs))
filter-elem p (x ∷ xs) i pi e with dec (i ==ℕ x) | dec (p x)
... | inl q | inl r = subst (λ l → T (elem i l)) (sym (T-if (p x) r)) (∨-l (i ==ℕ x) _ q)
... | inl q | inr r = ⊥-elim (r (subst (λ y → T (p y)) (==ℕ-sound i x q) pi))
... | inr q | inl r = subst (λ l → T (elem i l)) (sym (T-if (p x) r))
                        (∨-r (i ==ℕ x) _ (filter-elem p xs i pi (or-r′ (i ==ℕ x) _ q e)))
  where
  or-r′ : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r′ true  b n _ = ⊥-elim (n tt)
  or-r′ false b n p = p
... | inr q | inr r = subst (λ l → T (elem i l)) (sym (F-if (p x) r))
                        (filter-elem p xs i pi (or-r′ (i ==ℕ x) _ q e))
  where
  or-r′ : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r′ true  b n _ = ⊥-elim (n tt)
  or-r′ false b n p = p

lookup-none : ∀ (Φ : Ctx) i → (T (i <ℕ length Φ) → ⊥) → lookup Φ i ≡ nothing
lookup-none []      i       n = refl
lookup-none (A ∷ Φ) zero    n = ⊥-elim (n tt)
lookup-none (A ∷ Φ) (suc i) n = lookup-none Φ i n

vars-sup : ∀ Φ u k → T (elem k (varsT u)) → T (k <ℕ length Φ) → T (elem k (supVars Φ u))
vars-sup Φ u k e l =
  filter-elem (λ j → elem j (closeFrom Φ (length Φ) (varsT u))) (upTo (length Φ)) k
    (closeFrom-mono Φ (length Φ) (varsT u) k e) (upTo-elem (length Φ) k l)

-- Position in a list.
lookup-idx : ∀ i vs → T (elem i vs) → lookup vs (idx i vs) ≡ just i
lookup-idx i (v ∷ vs) p with dec (i ==ℕ v)
... | inl q = trans (cong (λ n → lookup (v ∷ vs) n) (T-if (i ==ℕ v) q)) (cong just (sym (==ℕ-sound i v q)))
... | inr q = trans (cong (λ n → lookup (v ∷ vs) n) (F-if (i ==ℕ v) q)) (lookup-idx i vs (or-r (i ==ℕ v) _ q p))
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

lookup-map : ∀ {A B : Set} (f : A → B) xs n → lookup (map f xs) n ≡ mapM f (lookup xs n)
lookup-map f []       n       = refl
lookup-map f (x ∷ xs) zero    = refl
lookup-map f (x ∷ xs) (suc n) = lookup-map f xs n

------------------------------------------------------------------------
-- Blanking the entries outside a support.

ptTy : CTy
ptTy = op ([] ▸ rep (disk 0))

blankFrom : Nat → List Nat → Ctx → Ctx
blankFrom n vs []       = []
blankFrom n vs (A ∷ As) = (if elem n vs then A else ptTy) ∷ blankFrom (suc n) vs As

lookup-blank : ∀ n vs Φ i → lookup (blankFrom n vs Φ) i ≡ mapM (λ A → if elem (n + i) vs then A else ptTy) (lookup Φ i)
lookup-blank n vs []       i       = refl
lookup-blank n vs (A ∷ As) zero    = cong (λ m → just (if elem m vs then A else ptTy)) (sym (+-zero n))
  where
  +-zero : ∀ m → m + 0 ≡ m
  +-zero zero    = refl
  +-zero (suc m) = cong suc (+-zero m)
lookup-blank n vs (A ∷ As) (suc i) =
  trans (lookup-blank (suc n) vs As i) (cong (λ m → mapM (λ A → if elem m vs then A else ptTy) (lookup As i)) (+-suc n i))
  where
  +-suc : ∀ m k → suc m + k ≡ m + suc k
  +-suc zero    k = refl
  +-suc (suc m) k = cong suc (+-suc m k)

blank : List Nat → Ctx → Ctx
blank = blankFrom 0

mapM-if : ∀ (b : Bool) (m : Maybe CTy) → T b → mapM (λ A → if b then A else ptTy) m ≡ m
mapM-if true nothing  _ = refl
mapM-if true (just A) _ = refl

agree-blank : ∀ Φ u → Agree Φ (blank (supVars Φ u) Φ) (varsT u)
agree-blank Φ u i p with dec (i <ℕ length Φ)
... | inl l = sym (trans (lookup-blank 0 vs Φ i) (mapM-if (elem i vs) (lookup Φ i) (vars-sup Φ u i p l)))
  where vs = supVars Φ u
... | inr l = trans (lookup-none Φ i l)
                (sym (trans (lookup-blank 0 vs Φ i)
                  (cong (mapM (λ A → if elem i vs then A else ptTy)) (lookup-none Φ i l))))
  where vs = supVars Φ u

------------------------------------------------------------------------
-- ren is well typed from the blanked context to the support context.

supCtx : List Nat → List Nat → Ctx → Ctx
supCtx as vs Φ = map (sY (renOf as vs)) (map (nthY Φ) vs)

just-inj′ : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-inj′ refl = refl

nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
nj ()

nthY-just : ∀ Φ i {A} → lookup Φ i ≡ just A → nthY Φ i ≡ A
nthY-just Φ i e with lookup Φ i
nthY-just Φ i refl | just A = refl

ren-typed : ∀ as vs Φ → supCtx as vs Φ ⊢ renOf as vs ∶ blank vs Φ
ren-typed as vs Φ = ⊢in app′
  where
  ren = renOf as vs
  app′ : ∀ i A → lookup (blank vs Φ) i ≡ just A → infer (supCtx as vs Φ) (Sub.tm ren i) ≡ just (sY ren A)
  app′ i A e with dec (elem i vs) | lookup Φ i in eΦ
  ... | inl q | just B =
    let eA : B ≡ A
        eA = just-inj′ (trans (sym (mapM-if (elem i vs) (just B) q))
                         (trans (cong (mapM (λ A → if elem i vs then A else ptTy)) (sym eΦ))
                           (trans (sym (lookup-blank 0 vs Φ i)) e)))
    in trans (cong (infer (supCtx as vs Φ)) (T-if (elem i vs) q))
         (trans (lookup-map (sY ren) (map (nthY Φ) vs) (idx i vs))
           (trans (cong (mapM (sY ren)) (lookup-map (nthY Φ) vs (idx i vs)))
             (trans (cong (λ m → mapM (sY ren) (mapM (nthY Φ) m)) (lookup-idx i vs q))
               (cong (λ X → just (sY ren X)) (trans (nthY-just Φ i eΦ) eA)))))
  ... | inl q | nothing = ⊥-elim (nj (trans (sym (trans (lookup-blank 0 vs Φ i) (cong (mapM (λ A → if elem i vs then A else ptTy)) eΦ))) e))
  ... | inr q | just B =
    let eA : ptTy ≡ A
        eA = just-inj′ (trans (cong just (sym (F-if (elem i vs) q)))
                         (trans (cong (mapM (λ A → if elem i vs then A else ptTy)) (sym eΦ))
                           (trans (sym (lookup-blank 0 vs Φ i)) e)))
    in trans (cong (infer (supCtx as vs Φ)) (F-if (elem i vs) q)) (cong (λ X → just (sY ren X)) eA)
  ... | inr q | nothing = ⊥-elim (nj (trans (sym (trans (lookup-blank 0 vs Φ i) (cong (mapM (λ A → if elem i vs then A else ptTy)) eΦ))) e))


------------------------------------------------------------------------
-- The theorem.

strengthen : ∀ k Φ u A → infer Φ u ≡ just A →
  infer (mctx (cidx (canon k Φ u))) (mterm (cidx (canon k Φ u)))
    ≡ just (sY (renOf (supAtoms k Φ u) (supVars Φ u)) A)
strengthen k Φ u A e =
  sub-infer (ren-typed as vs Φ) u A
    (trans (sym (infer-agree Φ (blank vs Φ) u (agree-blank Φ u))) e)
  where
  vs = supVars Φ u
  as = supAtoms k Φ u
