------------------------------------------------------------------------
-- Strengthening onto a canonical support (ledger S26j, step 2b): if
-- infer Φ u = A, then the canonical head of u types its own term at
-- the renamed type:
--
--   infer Φ′ (u[ren]) ≡ just (A[ren])
--
-- where Φ′ and u[ren] are the context and term of `canon k Φ u` and
-- ren = renOf (supAtoms Φ u) (supVars Φ u). The argument: u uses only
-- entries of its support (`vars-sup`), so by `infer-agree` it has the
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

addNew-mono : ∀ js i k → T (elem k js) → T (elem k (addNew js i))
addNew-mono js i k p with dec (elem i js)
... | inl q = subst T (sym (cong (elem k) (T-if (elem i js) q))) p
... | inr q = subst T (sym (cong (elem k) (F-if (elem i js) q))) (elem-++l k js (i ∷ []) p)

addNew-self : ∀ js i → T (elem i (addNew js i))
addNew-self js i with dec (elem i js)
... | inl q = subst T (sym (cong (elem i) (T-if (elem i js) q))) q
... | inr q = subst T (sym (cong (elem i) (F-if (elem i js) q)))
                (elem-++r i js (i ∷ []) (∨-l (i ==ℕ i) false (==ℕ-refl i)))

mutual
  visit-mono : ∀ Φ n acc j k → T (elem k acc) → T (elem k (visit Φ n acc j))
  visit-mono Φ zero    acc j k p = addNew-mono acc j k p
  visit-mono Φ (suc n) acc j k p with dec (elem j acc)
  ... | inl q = subst T (sym (cong (elem k) (T-if (elem j acc) q))) p
  ... | inr q = subst T (sym (cong (elem k) (F-if (elem j acc) q)))
                  (addNew-mono (visitAll Φ n acc (varsY (nthY Φ j))) j k (visitAll-mono Φ n acc (varsY (nthY Φ j)) k p))

  visitAll-mono : ∀ Φ n acc js k → T (elem k acc) → T (elem k (visitAll Φ n acc js))
  visitAll-mono Φ n acc []       k p = p
  visitAll-mono Φ n acc (j ∷ js) k p = visitAll-mono Φ n (visit Φ n acc j) js k (visit-mono Φ n acc j k p)

visit-self : ∀ Φ n acc j → T (elem j (visit Φ n acc j))
visit-self Φ zero    acc j = addNew-self acc j
visit-self Φ (suc n) acc j with dec (elem j acc)
... | inl q = subst T (sym (cong (elem j) (T-if (elem j acc) q))) q
... | inr q = subst T (sym (cong (elem j) (F-if (elem j acc) q))) (addNew-self (visitAll Φ n acc (varsY (nthY Φ j))) j)

visitAll-incl : ∀ Φ n acc js k → T (elem k js) → T (elem k (visitAll Φ n acc js))
visitAll-incl Φ n acc (j ∷ js) k p with dec (k ==ℕ j)
... | inl q = subst (λ x → T (elem x (visitAll Φ n (visit Φ n acc j) js))) (sym (==ℕ-sound k j q))
                (visitAll-mono Φ n (visit Φ n acc j) js j (visit-self Φ n acc j))
... | inr q = visitAll-incl Φ n (visit Φ n acc j) js k (or-r (k ==ℕ j) _ q p)
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p

vars-sup : ∀ Φ u k → T (elem k (varsT u)) → T (elem k (supVars Φ u))
vars-sup Φ u = visitAll-incl Φ (length Φ) [] (varsT u)

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

agree-blank : ∀ Φ vs xs → (∀ k → T (elem k xs) → T (elem k vs)) → Agree Φ (blank vs Φ) xs
agree-blank Φ vs xs inc i p =
  sym (trans (lookup-blank 0 vs Φ i) (mapM-if (elem i vs) (lookup Φ i) (inc i p)))

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
    ≡ just (sY (renOf (supAtoms Φ u) (supVars Φ u)) A)
strengthen k Φ u A e =
  sub-infer (ren-typed as vs Φ) u A
    (trans (sym (infer-agree Φ (blank vs Φ) u (agree-blank Φ vs (varsT u) (vars-sup Φ u)))) e)
  where
  vs = supVars Φ u
  as = supAtoms Φ u
