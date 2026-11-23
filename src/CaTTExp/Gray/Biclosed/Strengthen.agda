------------------------------------------------------------------------
-- The biclosed checker reads a context only at the variables a term
-- uses (ledger S26j, step 2b): if two contexts agree at every variable
-- of t, infer gives the same answer in both.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Strengthen where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Binder.MultimapCells using (varsT; varsTs; varsY)

------------------------------------------------------------------------
-- Agreement of two contexts on a list of variables.

Agree : Ctx → Ctx → List Nat → Set
Agree Φ Ψ xs = ∀ i → T (elem i xs) → lookup Φ i ≡ lookup Ψ i

∨-l : ∀ a b → T a → T (a ∨ b)
∨-l true  b _ = tt

∨-r : ∀ a b → T b → T (a ∨ b)
∨-r true  b _ = tt
∨-r false b p = p

elem-++l : ∀ i xs ys → T (elem i xs) → T (elem i (xs ++ ys))
elem-++l i (x ∷ xs) ys p with i ==ℕ x
... | true  = tt
... | false = elem-++l i xs ys p

elem-++r : ∀ i xs ys → T (elem i ys) → T (elem i (xs ++ ys))
elem-++r i []       ys p = p
elem-++r i (x ∷ xs) ys p = ∨-r (i ==ℕ x) _ (elem-++r i xs ys p)

agree-l : ∀ Φ Ψ xs ys → Agree Φ Ψ (xs ++ ys) → Agree Φ Ψ xs
agree-l Φ Ψ xs ys a i p = a i (elem-++l i xs ys p)

agree-r : ∀ Φ Ψ xs ys → Agree Φ Ψ (xs ++ ys) → Agree Φ Ψ ys
agree-r Φ Ψ xs ys a i p = a i (elem-++r i xs ys p)

------------------------------------------------------------------------
-- infer on comp, glue and cons, as plain functions of the recursive
-- results.

combC : Tm → List Tm → Maybe CTy → Maybe (List CTy) → Maybe CTy
combC f gs (just tf) (just tgs) = compTy f gs tf tgs
combC f gs _         _          = nothing

combG : Tm → Tm → Maybe CTy → Maybe CTy → Maybe CTy → Maybe CTy
combG am ap (just ta) (just tb) (just tx) = glueTop am ap ta tb tx
combG am ap _         _         _         = nothing

combL : Maybe CTy → Maybe (List CTy) → Maybe (List CTy)
combL (just A) (just As) = just (A ∷ As)
combL _        _         = nothing

comp-eq : ∀ Γ f gs → infer Γ (comp f gs) ≡ combC f gs (infer Γ f) (inferL Γ gs)
comp-eq Γ f gs with infer Γ f | inferL Γ gs
... | just _  | just _  = refl
... | just _  | nothing = refl
... | nothing | _       = refl

glue-eq : ∀ Γ am x ap → infer Γ (glue am x ap) ≡ combG am ap (infer Γ am) (infer Γ ap) (infer Γ x)
glue-eq Γ am x ap with infer Γ am | infer Γ ap | infer Γ x
... | just _  | just _  | just _  = refl
... | just _  | just _  | nothing = refl
... | just _  | nothing | _       = refl
... | nothing | _       | _       = refl

cons-eq : ∀ Γ t ts → inferL Γ (t ∷ ts) ≡ combL (infer Γ t) (inferL Γ ts)
cons-eq Γ t ts with infer Γ t | inferL Γ ts
... | just _  | just _  = refl
... | just _  | nothing = refl
... | nothing | _       = refl

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- The lemma.

mutual
  infer-agree : ∀ Φ Ψ t → Agree Φ Ψ (varsT t) → infer Φ t ≡ infer Ψ t
  infer-agree Φ Ψ (var i) a = a i (∨-l (i ==ℕ i) false (==ℕ-refl i))
  infer-agree Φ Ψ (mP U V) a = refl
  infer-agree Φ Ψ (eL A C) a = refl
  infer-agree Φ Ψ (eR A C) a = refl
  infer-agree Φ Ψ (pP Δ Θ) a = refl
  infer-agree Φ Ψ pt a = refl
  infer-agree Φ Ψ (iP Θ) a = refl
  infer-agree Φ Ψ (idt A) a = refl
  infer-agree Φ Ψ (comp f gs) a =
    trans (comp-eq Φ f gs)
      (trans (cong₂ (combC f gs) (infer-agree Φ Ψ f (agree-l Φ Ψ (varsT f) (varsTs gs) a))
                                 (inferL-agree Φ Ψ gs (agree-r Φ Ψ (varsT f) (varsTs gs) a)))
             (sym (comp-eq Ψ f gs)))
  infer-agree Φ Ψ (glue am x ap) a =
    let a₁  = agree-l Φ Ψ (varsT am) (varsT x ++ varsT ap) a
        a₂₃ = agree-r Φ Ψ (varsT am) (varsT x ++ varsT ap) a
        a₂  = agree-l Φ Ψ (varsT x) (varsT ap) a₂₃
        a₃  = agree-r Φ Ψ (varsT x) (varsT ap) a₂₃
    in trans (glue-eq Φ am x ap)
         (trans (cong₃ (combG am ap) (infer-agree Φ Ψ am a₁) (infer-agree Φ Ψ ap a₃) (infer-agree Φ Ψ x a₂))
                (sym (glue-eq Ψ am x ap)))
  infer-agree Φ Ψ (here t e φs ts) a =
    cong (λ b → if okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t) ∧ b
                then just (sY (instS φs ts) (goal t e)) else nothing)
         (argsOk-agree Φ Ψ (instS φs ts) ts (ctx t) a)

  inferL-agree : ∀ Φ Ψ ts → Agree Φ Ψ (varsTs ts) → inferL Φ ts ≡ inferL Ψ ts
  inferL-agree Φ Ψ []       a = refl
  inferL-agree Φ Ψ (t ∷ ts) a =
    trans (cons-eq Φ t ts)
      (trans (cong₂ combL (infer-agree Φ Ψ t (agree-l Φ Ψ (varsT t) (varsTs ts) a))
                          (inferL-agree Φ Ψ ts (agree-r Φ Ψ (varsT t) (varsTs ts) a)))
             (sym (cons-eq Ψ t ts)))

  argsOk-agree : ∀ Φ Ψ σ ts As → Agree Φ Ψ (varsTs ts) → argsOk Φ σ ts As ≡ argsOk Ψ σ ts As
  argsOk-agree Φ Ψ σ []       []       a = refl
  argsOk-agree Φ Ψ σ []       (_ ∷ _)  a = refl
  argsOk-agree Φ Ψ σ (_ ∷ _)  []       a = refl
  argsOk-agree Φ Ψ σ (x ∷ xs) (A ∷ As) a =
    cong₂ (λ m b → eqMaybeTy m (sY σ A) ∧ b)
      (infer-agree Φ Ψ x (agree-l Φ Ψ (varsT x) (varsTs xs) a))
      (argsOk-agree Φ Ψ σ xs As (agree-r Φ Ψ (varsT x) (varsTs xs) a))

------------------------------------------------------------------------
-- A term that infers uses only variables of its context.

Below : Nat → List Nat → Set
Below n xs = ∀ i → T (elem i xs) → T (i <ℕ n)

below-++ : ∀ n xs ys → Below n xs → Below n ys → Below n (xs ++ ys)
below-++ n []       ys bx by i p = by i p
below-++ n (x ∷ xs) ys bx by i p with i ==ℕ x in e
... | true  = bx i (subst (λ b → T (b ∨ elem i xs)) (sym e) tt)
... | false = below-++ n xs ys (λ j q → bx j (∨-r (j ==ℕ x) _ q)) by i p

lookup-below : ∀ (Γ : Ctx) i {A} → lookup Γ i ≡ just A → T (i <ℕ length Γ)
lookup-below (B ∷ Γ) zero    e = tt
lookup-below (B ∷ Γ) (suc i) e = lookup-below Γ i e

private
  nj′ : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj′ ()

  combC-inv : ∀ f gs m ms {A} → combC f gs m ms ≡ just A →
              Σ CTy (λ tf → m ≡ just tf) × Σ (List CTy) (λ tgs → ms ≡ just tgs)
  combC-inv f gs (just tf) (just tgs) e = (tf , refl) , (tgs , refl)
  combC-inv f gs (just tf) nothing    ()
  combC-inv f gs nothing   _          ()

  combG-inv : ∀ am ap a b x {A} → combG am ap a b x ≡ just A →
              Σ CTy (λ ta → a ≡ just ta) × Σ CTy (λ tb → b ≡ just tb) × Σ CTy (λ tx → x ≡ just tx)
  combG-inv am ap (just a) (just b) (just x) e = (a , refl) , (b , refl) , (x , refl)
  combG-inv am ap (just a) (just b) nothing ()
  combG-inv am ap (just a) nothing _ ()
  combG-inv am ap nothing _ _ ()

  combL-inv : ∀ m ms {As} → combL m ms ≡ just As →
              Σ CTy (λ A → m ≡ just A) × Σ (List CTy) (λ Bs → ms ≡ just Bs)
  combL-inv (just A) (just Bs) e = (A , refl) , (Bs , refl)
  combL-inv (just A) nothing ()
  combL-inv nothing _ ()

  if-just : ∀ (b : Bool) {X : Set} {x : X} {y : X} → (if b then just x else nothing) ≡ just y → T b
  if-just true  _ = tt
  if-just false ()

  eqMaybe-just : ∀ m B → T (eqMaybeTy m B) → Σ CTy (λ A → m ≡ just A)
  eqMaybe-just (just A) B _ = A , refl

  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

mutual
  infer-scope : ∀ Γ t {A} → infer Γ t ≡ just A → Below (length Γ) (varsT t)
  infer-scope Γ (var i) e j p with j ==ℕ i in q
  ... | true  = subst (λ x → T (x <ℕ length Γ)) (sym (==ℕ-sound j i (subst T (sym q) tt))) (lookup-below Γ i e)
  infer-scope Γ (comp f gs) e =
    let ((tf , ef) , (tgs , egs)) = combC-inv f gs _ _ (trans (sym (comp-eq Γ f gs)) e)
    in below-++ (length Γ) (varsT f) (varsTs gs) (infer-scope Γ f ef) (inferL-scope Γ gs egs)
  infer-scope Γ (glue am x ap) e =
    let ((ta , ea) , (tb , eb) , (tx , ex)) = combG-inv am ap _ _ _ (trans (sym (glue-eq Γ am x ap)) e)
    in below-++ (length Γ) (varsT am) (varsT x ++ varsT ap) (infer-scope Γ am ea)
         (below-++ (length Γ) (varsT x) (varsT ap) (infer-scope Γ x ex) (infer-scope Γ ap eb))
  infer-scope Γ (here t g φs ts) e =
    let c = okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t)
    in argsOk-scope Γ (instS φs ts) ts (ctx t)
         (∧-r (length ts ==ℕ nCtx t) _ (∧-r (length φs ==ℕ nObj t) _ (∧-r (okT t) _
           (if-just (okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t) ∧ argsOk Γ (instS φs ts) ts (ctx t)) e))))
  infer-scope Γ (mP _ _) e i ()
  infer-scope Γ (eL _ _) e i ()
  infer-scope Γ (eR _ _) e i ()
  infer-scope Γ (pP _ _) e i ()
  infer-scope Γ pt       e i ()
  infer-scope Γ (iP _)   e i ()
  infer-scope Γ (idt _)  e i ()

  inferL-scope : ∀ Γ ts {As} → inferL Γ ts ≡ just As → Below (length Γ) (varsTs ts)
  inferL-scope Γ []       e i ()
  inferL-scope Γ (t ∷ ts) e =
    let ((A , eA) , (Bs , eBs)) = combL-inv _ _ (trans (sym (cons-eq Γ t ts)) e)
    in below-++ (length Γ) (varsT t) (varsTs ts) (infer-scope Γ t eA) (inferL-scope Γ ts eBs)

  argsOk-scope : ∀ Γ σ ts As → T (argsOk Γ σ ts As) → Below (length Γ) (varsTs ts)
  argsOk-scope Γ σ []       _        p i ()
  argsOk-scope Γ σ (x ∷ xs) []       ()
  argsOk-scope Γ σ (x ∷ xs) (A ∷ As) p =
    let (B , eB) = eqMaybe-just (infer Γ x) (sY σ A) (∧-l _ _ p)
    in below-++ (length Γ) (varsT x) (varsTs xs) (infer-scope Γ x eB) (argsOk-scope Γ σ xs As (∧-r _ _ p))

wf-scope : ∀ Γ A → T (wf Γ A) → Below (length Γ) (varsY A)
wf-scope Γ (op _) p i ()
wf-scope Γ (hom m g A s t) p =
  let pA = ∧-l (wf Γ A) _ p
      p₂ = ∧-r (wf Γ A) _ p
      (B , eB) = eqMaybe-just (infer Γ s) A (∧-l _ _ p₂)
      (C , eC) = eqMaybe-just (infer Γ t) A (∧-r _ _ p₂)
  in below-++ (length Γ) (varsY A) (varsT s ++ varsT t) (wf-scope Γ A pA)
       (below-++ (length Γ) (varsT s) (varsT t) (infer-scope Γ s eB) (infer-scope Γ t eC))

-- In a well-formed context, entry j's type uses only entries below j.
wfFrom-scope : ∀ acc Φ p {A} → T (wfCtxFrom acc Φ) → lookup Φ p ≡ just A →
               Below (length acc + p) (varsY A)
wfFrom-scope acc (B ∷ Φ) zero    w refl =
  subst (λ n → Below n (varsY B)) (sym (+0 (length acc))) (wf-scope acc B (∧-l _ _ w))
  where
  +0 : ∀ n → n + 0 ≡ n
  +0 zero    = refl
  +0 (suc n) = cong suc (+0 n)
wfFrom-scope acc (B ∷ Φ) (suc p) {A} w e =
  subst (λ n → Below n (varsY A)) (len-snoc acc B p)
    (wfFrom-scope (acc ++ (B ∷ [])) Φ p (∧-r _ _ w) e)
  where
  len-snoc : ∀ (acc : Ctx) B p → length (acc ++ (B ∷ [])) + p ≡ length acc + suc p
  len-snoc []      B p = refl
  len-snoc (_ ∷ a) B p = cong suc (len-snoc a B p)

wf-deps : ∀ Φ j {A} → T (wfCtx Φ) → lookup Φ j ≡ just A → Below j (varsY A)
wf-deps Φ j w e = wfFrom-scope [] Φ j w e
