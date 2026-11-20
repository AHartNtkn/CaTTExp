------------------------------------------------------------------------
-- Scoping of the biclosed syntax, and the substitution laws of
-- coherence terms.
--
-- A coherence term here t e φs ts stands for goal e of template t under
-- instS φs ts.  Its substitution laws need the template to be well
-- scoped: every object variable of its context and goals is below
-- nObj t and every context variable below nCtx t.
--
-- Main results (no postulates):
--   * agree-sY  : substitutions that agree on the scope of A act on A
--                 alike;
--   * inst-sY   : τ after instS φs ts is instS (φs[τ]) (ts[τ]) on types
--                 scoped by the two lists;
--   * inst-id   : the identity instance acts as the identity;
--   * ctx-scoped, cgoal-scoped, egoal-scoped : every okT template is
--                 well scoped;
--   * cterm-typed : the identity instance of c is well typed in the
--                 template's own context, with type cgoal t.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Scope where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import Agda.Builtin.Nat using (_*_)

------------------------------------------------------------------------
-- Arithmetic on leq

lt : Nat → Nat → Bool
lt i k = leq (suc i) k

leq-refl : ∀ n → T (leq n n)
leq-refl zero    = tt
leq-refl (suc n) = leq-refl n

leq-trans : ∀ a b c → T (leq a b) → T (leq b c) → T (leq a c)
leq-trans zero    b       c       _ _ = tt
leq-trans (suc a) (suc b) (suc c) p q = leq-trans a b c p q

leq-suc : ∀ a b → T (leq a b) → T (leq a (suc b))
leq-suc zero    b       _ = tt
leq-suc (suc a) (suc b) p = leq-suc a b p

leq-+ʳ : ∀ a b → T (leq a (a + b))
leq-+ʳ zero    b = tt
leq-+ʳ (suc a) b = leq-+ʳ a b

leq-+ˡ : ∀ a b → T (leq b (a + b))
leq-+ˡ zero    b = leq-refl b
leq-+ˡ (suc a) b = leq-suc b (a + b) (leq-+ˡ a b)

leq-mono : ∀ a b c → T (leq a b) → T (leq (a + c) (b + c))
leq-mono zero    b       c _ = leq-+ˡ b c
leq-mono (suc a) (suc b) c p = leq-mono a b c p

lt-suc : ∀ i → T (lt i (suc i))
lt-suc i = leq-refl i

-- offsets inside a block: o + 6j < m when 6 + 6j ≤ m and o < 6
lt-pos : ∀ o j m → T (lt o 6) → T (leq (suc j * 6) m) → T (lt (o + j * 6) m)
lt-pos o j m p q = leq-trans (suc o + j * 6) (6 + j * 6) m (leq-mono (suc o) 6 (j * 6) p) q

leq-step : ∀ j m → T (leq (suc j * 6) m) → T (leq (j * 6) m)
leq-step j m p = leq-trans (j * 6) (6 + j * 6) m (leq-+ˡ 6 (j * 6)) p

------------------------------------------------------------------------
-- Scope checks: object variables below k, context variables below m

scF : Nat → Fm → Bool
scF k (obj i)  = lt i k
scF k (rep _)  = true
scF k (a ⊗ b)  = scF k a ∧ scF k b
scF k (a \\ b) = scF k a ∧ scF k b
scF k (a // b) = scF k a ∧ scF k b

scFs : Nat → List Fm → Bool
scFs k []       = true
scFs k (a ∷ as) = scF k a ∧ scFs k as

scM : Nat → MTy → Bool
scM k (xs ▸ z) = scFs k xs ∧ scF k z

mutual
  scT : Nat → Nat → Tm → Bool
  scT k m (var i)          = lt i m
  scT k m (mP U V)         = scF k U ∧ scF k V
  scT k m (eL A C)         = scF k A ∧ scF k C
  scT k m (eR A C)         = scF k A ∧ scF k C
  scT k m (pP _ _)         = true
  scT k m pt               = true
  scT k m (idt A)          = scF k A
  scT k m (comp f gs)      = scT k m f ∧ scTs k m gs
  scT k m (glue a x b)     = scT k m a ∧ scT k m x ∧ scT k m b
  scT k m (here _ _ φs ts) = scFs k φs ∧ scTs k m ts

  scTs : Nat → Nat → List Tm → Bool
  scTs k m []       = true
  scTs k m (x ∷ xs) = scT k m x ∧ scTs k m xs

scY : Nat → Nat → CTy → Bool
scY k m (op M)          = scM k M
scY k m (hom _ _ A s t) = scY k m A ∧ scT k m s ∧ scT k m t

private
  ∧ˡ : ∀ {a b} → T (a ∧ b) → T a
  ∧ˡ = ∧-fst
  ∧ʳ : ∀ {a b} → T (a ∧ b) → T b
  ∧ʳ {a} = ∧-snd {a}

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Agreement on a scope

record Agree (k m : Nat) (σ τ : Sub) : Set where
  constructor agree
  field
    agF : ∀ i → T (lt i k) → fo σ i ≡ fo τ i
    agT : ∀ i → T (lt i m) → tm σ i ≡ tm τ i
open Agree public

module _ {k m : Nat} {σ τ : Sub} (ag : Agree k m σ τ) where
  agree-sF : ∀ a → T (scF k a) → sF (fo σ) a ≡ sF (fo τ) a
  agree-sF (obj i)  p = agF ag i p
  agree-sF (rep _)  p = refl
  agree-sF (a ⊗ b)  p = cong₂ _⊗_ (agree-sF a (∧ˡ p)) (agree-sF b (∧ʳ {scF k a} p))
  agree-sF (a \\ b) p = cong₂ _\\_ (agree-sF a (∧ˡ p)) (agree-sF b (∧ʳ {scF k a} p))
  agree-sF (a // b) p = cong₂ _//_ (agree-sF a (∧ˡ p)) (agree-sF b (∧ʳ {scF k a} p))

  agree-sFs : ∀ as → T (scFs k as) → sFs (fo σ) as ≡ sFs (fo τ) as
  agree-sFs []       _ = refl
  agree-sFs (a ∷ as) p = cong₂ _∷_ (agree-sF a (∧ˡ p)) (agree-sFs as (∧ʳ {scF k a} p))

  agree-sM : ∀ M → T (scM k M) → sM (fo σ) M ≡ sM (fo τ) M
  agree-sM (xs ▸ z) p = cong₂ _▸_ (agree-sFs xs (∧ˡ p)) (agree-sF z (∧ʳ {scFs k xs} p))

  mutual
    agree-sT : ∀ x → T (scT k m x) → sT σ x ≡ sT τ x
    agree-sT (var i)  p = agT ag i p
    agree-sT (mP U V) p = cong₂ mP (agree-sF U (∧ˡ p)) (agree-sF V (∧ʳ {scF k U} p))
    agree-sT (eL A C) p = cong₂ eL (agree-sF A (∧ˡ p)) (agree-sF C (∧ʳ {scF k A} p))
    agree-sT (eR A C) p = cong₂ eR (agree-sF A (∧ˡ p)) (agree-sF C (∧ʳ {scF k A} p))
    agree-sT (pP _ _) p = refl
    agree-sT pt       p = refl
    agree-sT (idt A)  p = cong idt (agree-sF A p)
    agree-sT (comp f gs) p =
      cong₂ comp (agree-sT f (∧ˡ p)) (agree-sTs gs (∧ʳ {scT k m f} p))
    agree-sT (glue a x b) p =
      let q = ∧ʳ {scT k m a} p in
      cong₃ glue (agree-sT a (∧ˡ p)) (agree-sT x (∧ˡ q)) (agree-sT b (∧ʳ {scT k m x} q))
    agree-sT (here t e φs ts) p =
      cong₂ (here t e) (agree-sFs φs (∧ˡ p)) (agree-sTs ts (∧ʳ {scFs k φs} p))

    agree-sTs : ∀ xs → T (scTs k m xs) → sTs σ xs ≡ sTs τ xs
    agree-sTs []       _ = refl
    agree-sTs (x ∷ xs) p = cong₂ _∷_ (agree-sT x (∧ˡ p)) (agree-sTs xs (∧ʳ {scT k m x} p))

  agree-sY : ∀ A → T (scY k m A) → sY σ A ≡ sY τ A
  agree-sY (op M) p = cong op (agree-sM M p)
  agree-sY (hom md g A s t) p =
    let q = ∧ʳ {scY k m A} p in
    cong₃ (hom md g) (agree-sY A (∧ˡ p)) (agree-sT s (∧ˡ q)) (agree-sT t (∧ʳ {scT k m s} q))

------------------------------------------------------------------------
-- The instance substitution

nthF-sFs : ∀ φ as i → T (lt i (length as)) → sF φ (nthF as i) ≡ nthF (sFs φ as) i
nthF-sFs φ (a ∷ as) zero    _ = refl
nthF-sFs φ (a ∷ as) (suc i) p = nthF-sFs φ as i p

nthT-sTs : ∀ σ xs i → T (lt i (length xs)) → sT σ (nthT xs i) ≡ nthT (sTs σ xs) i
nthT-sTs σ (x ∷ xs) zero    _ = refl
nthT-sTs σ (x ∷ xs) (suc i) p = nthT-sTs σ xs i p

inst-⨾ : ∀ φs ts τ →
  Agree (length φs) (length ts) (instS φs ts ⨾ τ) (instS (sFs (fo τ) φs) (sTs τ ts))
inst-⨾ φs ts τ = agree (nthF-sFs (fo τ) φs) (nthT-sTs τ ts)

-- substituting into an instance
inst-sY : ∀ φs ts τ A → T (scY (length φs) (length ts) A) →
          sY τ (sY (instS φs ts) A) ≡ sY (instS (sFs (fo τ) φs) (sTs τ ts)) A
inst-sY φs ts τ A p =
  trans (Comp.sY-⨾ (instS φs ts) τ A) (agree-sY (inst-⨾ φs ts τ) A p)

inst-sT : ∀ φs ts τ x → T (scT (length φs) (length ts) x) →
          sT τ (sT (instS φs ts) x) ≡ sT (instS (sFs (fo τ) φs) (sTs τ ts)) x
inst-sT φs ts τ x p =
  trans (Comp.sT-⨾ (instS φs ts) τ x) (agree-sT (inst-⨾ φs ts τ) x p)

-- the identity lists
length-objsFrom : ∀ a k → length (objsFrom a k) ≡ k
length-objsFrom a zero    = refl
length-objsFrom a (suc k) = cong suc (length-objsFrom (suc a) k)

length-varsFrom : ∀ a k → length (varsFrom a k) ≡ k
length-varsFrom a zero    = refl
length-varsFrom a (suc k) = cong suc (length-varsFrom (suc a) k)

private
  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

nth-objsFrom : ∀ a k i → T (lt i k) → nthF (objsFrom a k) i ≡ obj (a + i)
nth-objsFrom a (suc k) zero    _ = cong obj (sym (+-zero a))
nth-objsFrom a (suc k) (suc i) p =
  trans (nth-objsFrom (suc a) k i p) (cong obj (sym (+-suc a i)))

nth-varsFrom : ∀ a k i → T (lt i k) → nthT (varsFrom a k) i ≡ var (a + i)
nth-varsFrom a (suc k) zero    _ = cong var (sym (+-zero a))
nth-varsFrom a (suc k) (suc i) p =
  trans (nth-varsFrom (suc a) k i p) (cong var (sym (+-suc a i)))

inst-id-agree : ∀ k m → Agree k m (instS (objsFrom 0 k) (varsFrom 0 m)) idS
inst-id-agree k m = agree (λ i p → nth-objsFrom 0 k i p) (λ i p → nth-varsFrom 0 m i p)

inst-id : ∀ k m A → T (scY k m A) → sY (instS (objsFrom 0 k) (varsFrom 0 m)) A ≡ A
inst-id k m A p = trans (agree-sY (inst-id-agree k m) A p) (sY-id A)

------------------------------------------------------------------------
-- Weakening of scopes

scF-up : ∀ k k′ a → T (leq k k′) → T (scF k a) → T (scF k′ a)
scF-up k k′ (obj i)  le p = leq-trans (suc i) k k′ p le
scF-up k k′ (rep _)  le p = tt
scF-up k k′ (a ⊗ b)  le p = ∧-intro (scF-up k k′ a le (∧ˡ p)) (scF-up k k′ b le (∧ʳ {scF k a} p))
scF-up k k′ (a \\ b) le p = ∧-intro (scF-up k k′ a le (∧ˡ p)) (scF-up k k′ b le (∧ʳ {scF k a} p))
scF-up k k′ (a // b) le p = ∧-intro (scF-up k k′ a le (∧ˡ p)) (scF-up k k′ b le (∧ʳ {scF k a} p))

scFs-up : ∀ k k′ as → T (leq k k′) → T (scFs k as) → T (scFs k′ as)
scFs-up k k′ []       le p = tt
scFs-up k k′ (a ∷ as) le p = ∧-intro (scF-up k k′ a le (∧ˡ p)) (scFs-up k k′ as le (∧ʳ {scF k a} p))

scM-up : ∀ k k′ M → T (leq k k′) → T (scM k M) → T (scM k′ M)
scM-up k k′ (xs ▸ z) le p = ∧-intro (scFs-up k k′ xs le (∧ˡ p)) (scF-up k k′ z le (∧ʳ {scFs k xs} p))

module _ (k : Nat) where
  mutual
    scT-up : ∀ m m′ x → T (leq m m′) → T (scT k m x) → T (scT k m′ x)
    scT-up m m′ (var i)  le p = leq-trans (suc i) m m′ p le
    scT-up m m′ (mP U V) le p = p
    scT-up m m′ (eL A C) le p = p
    scT-up m m′ (eR A C) le p = p
    scT-up m m′ (pP _ _) le p = tt
    scT-up m m′ pt       le p = tt
    scT-up m m′ (idt A)  le p = p
    scT-up m m′ (comp f gs) le p =
      ∧-intro (scT-up m m′ f le (∧ˡ p)) (scTs-up m m′ gs le (∧ʳ {scT k m f} p))
    scT-up m m′ (glue a x b) le p =
      let q = ∧ʳ {scT k m a} p in
      ∧-intro (scT-up m m′ a le (∧ˡ p))
        (∧-intro (scT-up m m′ x le (∧ˡ q)) (scT-up m m′ b le (∧ʳ {scT k m x} q)))
    scT-up m m′ (here _ _ φs ts) le p =
      ∧-intro (∧ˡ p) (scTs-up m m′ ts le (∧ʳ {scFs k φs} p))

    scTs-up : ∀ m m′ xs → T (leq m m′) → T (scTs k m xs) → T (scTs k m′ xs)
    scTs-up m m′ []       le p = tt
    scTs-up m m′ (x ∷ xs) le p =
      ∧-intro (scT-up m m′ x le (∧ˡ p)) (scTs-up m m′ xs le (∧ʳ {scT k m x} p))

  scY-up : ∀ m m′ A → T (leq m m′) → T (scY k m A) → T (scY k m′ A)
  scY-up m m′ (op M) le p = p
  scY-up m m′ (hom _ _ A s t) le p =
    let q = ∧ʳ {scY k m A} p in
    ∧-intro (scY-up m m′ A le (∧ˡ p))
      (∧-intro (scT-up m m′ s le (∧ˡ q)) (scT-up m m′ t le (∧ʳ {scT k m s} q)))

------------------------------------------------------------------------
-- Canonical rows are scoped

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

All-++ : ∀ {A : Set} {P : A → Set} xs {ys} → All P (xs ++ ys) → All P xs × All P ys
All-++ []       ps       = [] , ps
All-++ (x ∷ xs) (p ∷ ps) = let (a , b) = All-++ xs ps in (p ∷ a) , b

uncons : ∀ {A : Set} {P : A → Set} {x xs} → All P (x ∷ xs) → P x × All P xs
uncons (p ∷ ps) = p , ps

one : ∀ {A : Set} {P : A → Set} {x} → All P (x ∷ []) → P x
one (p ∷ []) = p

All-++⁺ : ∀ {A : Set} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
All-++⁺ []       qs = qs
All-++⁺ (p ∷ ps) qs = p ∷ All-++⁺ ps qs

-- atoms of a canonical list are below its counter plus its length
canon-sc : ∀ k fs → T (canonFrom k fs) → All (λ a → T (scF (k + length fs) a)) fs
canon-sc k []            _ = []
canon-sc k (obj i ∷ fs)  p
  rewrite ==ℕ-sound i k (∧ˡ p) | +-suc k (length fs) =
  leq-+ʳ (suc k) (length fs) ∷ canon-sc (suc k) fs (∧ʳ {i ==ℕ k} p)
canon-sc k (rep s ∷ fs)  p rewrite +-suc k (length fs) =
  tt ∷ All-mono fs (canon-sc k fs p)
  where
  All-mono : ∀ gs → All (λ a → T (scF (k + length fs) a)) gs →
             All (λ a → T (scF (suc (k + length fs)) a)) gs
  All-mono []       []       = []
  All-mono (g ∷ gs) (q ∷ qs) =
    scF-up (k + length fs) (suc (k + length fs)) g
      (leq-suc (k + length fs) (k + length fs) (leq-refl (k + length fs))) q ∷ All-mono gs qs
canon-sc k (_ ⊗ _ ∷ fs)  ()
canon-sc k (_ \\ _ ∷ fs) ()
canon-sc k (_ // _ ∷ fs) ()

All→scFs : ∀ {k} xs → All (λ a → T (scF k a)) xs → T (scFs k xs)
All→scFs []       []       = tt
All→scFs (x ∷ xs) (p ∷ ps) = ∧-intro p (All→scFs xs ps)

All→ids : ∀ {k m} xs → All (λ a → T (scF k a)) xs → T (scTs k m (ids xs))
All→ids []       []       = tt
All→ids (x ∷ xs) (p ∷ ps) = ∧-intro p (All→ids xs ps)

scTs-++ : ∀ {k m} xs ys → T (scTs k m xs) → T (scTs k m ys) → T (scTs k m (xs ++ ys))
scTs-++ []       ys _ q = q
scTs-++ {k} {m} (x ∷ xs) ys p q = ∧-intro (∧ˡ p) (scTs-++ xs ys (∧ʳ {scT k m x} p) q)

scFs-++ : ∀ {k} xs ys → T (scFs k xs) → T (scFs k ys) → T (scFs k (xs ++ ys))
scFs-++ []       ys _ q = q
scFs-++ {k} (x ∷ xs) ys p q = ∧-intro (∧ˡ p) (scFs-++ xs ys (∧ʳ {scF k x} p) q)

-- the formulas of a row, all scoped by k
RowSc : Nat → Row → Set
RowSc k ρ = All (λ a → T (scF k a)) (fmsOf ρ)

row-sc : ∀ t → T (okT t) → RowSc (nObj t) (row t)
row-sc (tmpl ρ g m zero)    ok = canon-sc 0 (fmsOf ρ) (∧ˡ (∧ˡ ok))
row-sc (tmpl ρ g m (suc n)) ok = canon-sc 0 (fmsOf ρ) (∧ˡ (∧ˡ ok))

module RowScope (k : Nat) where
  H-sc : ∀ ρ → RowSc k ρ → T (scM k (H ρ))
  H-sc (pairR L U V R Z) p =
    let (pL , q) = All-++ L p ; (pU , q₁) = uncons q ; (pV , q′) = uncons q₁ ; (pR , qz) = All-++ R q′ ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (∧-intro (∧-intro pU pV) (All→scFs R pR))) pZ
  H-sc (probeR L Δ Θ R Z) p =
    let (pL , q) = All-++ L p ; (pR , qz) = All-++ R q ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (∧-intro tt (All→scFs R pR))) pZ
  H-sc (unitR L R Z) p =
    let (pL , q) = All-++ L p ; (pR , qz) = All-++ R q ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (∧-intro tt (All→scFs R pR))) pZ
  H-sc (evLR Φ A C) (pA ∷ q) =
    let (pΦ , qc) = All-++ Φ q ; pC = one qc in ∧-intro (All→scFs Φ pΦ) (∧-intro pA pC)
  H-sc (evRR Φ A C) p =
    let (pΦ , qa) = All-++ Φ p ; (pA , qc) = uncons qa ; pC = one qc in ∧-intro (All→scFs Φ pΦ) (∧-intro pC pA)

  B-sc : ∀ ρ → RowSc k ρ → T (scM k (B ρ))
  B-sc (pairR L U V R Z) p =
    let (pL , q) = All-++ L p ; (pU , q₁) = uncons q ; (pV , q′) = uncons q₁ ; (pR , qz) = All-++ R q′ ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (∧-intro pU (∧-intro pV (All→scFs R pR)))) pZ
  B-sc (probeR L Δ Θ R Z) p =
    let (pL , q) = All-++ L p ; (pR , qz) = All-++ R q ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (∧-intro tt (∧-intro tt (All→scFs R pR)))) pZ
  B-sc (unitR L R Z) p =
    let (pL , q) = All-++ L p ; (pR , qz) = All-++ R q ; pZ = one qz in
    ∧-intro (scFs-++ L _ (All→scFs L pL) (All→scFs R pR)) pZ
  B-sc (evLR Φ A C) (pA ∷ q) =
    let (pΦ , qc) = All-++ Φ q ; pC = one qc in ∧-intro (∧-intro pA (All→scFs Φ pΦ)) pC
  B-sc (evRR Φ A C) p =
    let (pΦ , qa) = All-++ Φ p ; (pA , qc) = uncons qa ; pC = one qc in
    ∧-intro (scFs-++ Φ _ (All→scFs Φ pΦ) (∧-intro pA tt)) pC

  rmap-sc : ∀ {m} ρ x → RowSc k ρ → T (scT k m x) → T (scT k m (rmap ρ x))
  rmap-sc {m} (pairR L U V R Z) x p px =
    let (pL , q) = All-++ L p ; (pU , q₁) = uncons q ; (pV , q′) = uncons q₁ ; (pR , _) = All-++ R q′ in
    ∧-intro px (scTs-++ (ids L) _ (All→ids L pL) (∧-intro (∧-intro pU pV) (All→ids R pR)))
  rmap-sc {m} (probeR L Δ Θ R Z) x p px =
    let (pL , q) = All-++ L p ; (pR , _) = All-++ R q in
    ∧-intro px (scTs-++ (ids L) _ (All→ids L pL) (∧-intro tt (All→ids R pR)))
  rmap-sc {m} (unitR L R Z) x p px =
    let (pL , q) = All-++ L p ; (pR , _) = All-++ R q in
    ∧-intro px (scTs-++ (ids L) _ (All→ids L pL) (∧-intro tt (All→ids R pR)))
  rmap-sc {m} (evLR Φ A C) x (pA ∷ q) px =
    let (_ , qc) = All-++ Φ q ; pC = one qc in
    ∧-intro (∧-intro pA pC) (∧-intro pA (∧-intro px tt))
  rmap-sc {m} (evRR Φ A C) x p px =
    let (_ , qa) = All-++ Φ p ; (pA , qc) = uncons qa ; pC = one qc in
    ∧-intro (∧-intro pA pC) (∧-intro px (∧-intro pA tt))

------------------------------------------------------------------------
-- Templates are scoped

module TmplScope (t : Tmpl) (ok : T (okT t)) where
  open RowScope (nObj t)
  private
    K = nObj t
    ρ = row t
    rs = row-sc t ok

  -- every variable of level j or below lies below 6(j+1)
  tyU-sc : ∀ j m → T (leq (j * 6) m) → T (scY K m (tyU t j))
  tyU-sc zero    m _ = H-sc ρ rs
  tyU-sc (suc j) m p =
    ∧-intro (tyU-sc j m (leq-step j m p))
      (∧-intro (lt-pos 0 j m tt p) (lt-pos 1 j m tt p))

  tyB-sc : ∀ j m → T (leq (j * 6) m) → T (scY K m (tyB t j))
  tyB-sc zero    m _ = B-sc ρ rs
  tyB-sc (suc j) m p =
    ∧-intro (tyB-sc j m (leq-step j m p))
      (∧-intro (lt-pos 2 j m tt p) (lt-pos 3 j m tt p))

  tyRU-sc : ∀ j m → T (leq (j * 6) m) → T (scY K m (tyRU t j))
  tyRU-sc zero    m _ = B-sc ρ rs
  tyRU-sc (suc j) m p =
    ∧-intro (tyRU-sc j m (leq-step j m p))
      (∧-intro (rmap-sc ρ (var (uM j)) rs (lt-pos 0 j m tt p))
               (rmap-sc ρ (var (uP j)) rs (lt-pos 1 j m tt p)))

  chain-sc : ∀ j m y → T (leq (j * 6) m) → T (scT K m y) → T (scT K m (chain t j y))
  chain-sc zero    m y _ py = py
  chain-sc (suc j) m y p py =
    ∧-intro (lt-pos 4 j m tt p)
      (∧-intro (chain-sc j m y (leq-step j m p) py) (lt-pos 5 j m tt p))

  block-sc : ∀ j m → T (leq (suc j * 6) m) → All (λ A → T (scY K m A)) (block t j)
  block-sc j m p =
    let p′ = leq-step j m p in
    tyU-sc j m p′ ∷ tyU-sc j m p′ ∷ tyB-sc j m p′ ∷ tyB-sc j m p′
    ∷ ∧-intro (tyRU-sc j m p′)
        (∧-intro (rmap-sc ρ (var (uM j)) rs (lt-pos 0 j m tt p))
                 (chain-sc j m (var (bM j)) p′ (lt-pos 2 j m tt p)))
    ∷ ∧-intro (tyRU-sc j m p′)
        (∧-intro (rmap-sc ρ (var (uP j)) rs (lt-pos 1 j m tt p))
                 (chain-sc j m (var (bP j)) p′ (lt-pos 3 j m tt p)))
    ∷ []

  levels-sc : ∀ j m → T (leq (j * 6) m) → All (λ A → T (scY K m A)) (levels t j)
  levels-sc zero    m _ = []
  levels-sc (suc j) m p = All-++⁺ (levels-sc j m (leq-step j m p)) (block-sc j m p)

  -- the length of the context
  length-block : ∀ j → length (block t j) ≡ 6
  length-block j = refl

  length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm zero    b = sym (+-zero b)
  +-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

  length-levels : ∀ j → length (levels t j) ≡ j * 6
  length-levels zero    = refl
  length-levels (suc j) =
    trans (length-++ (levels t j) (block t j))
          (trans (cong (_+ 6) (length-levels j)) (+-comm (j * 6) 6))

  nCtx-eq : nCtx t ≡ suc (dimn t * 6)
  nCtx-eq = trans (length-++ (levels t (dimn t)) (tyB t (dimn t) ∷ []))
                  (trans (cong (_+ 1) (length-levels (dimn t))) (+-comm (dimn t * 6) 1))

  private
    n = dimn t
    M = nCtx t
    nM : T (leq (n * 6) M)
    nM = subst (λ q → T (leq (n * 6) q)) (sym nCtx-eq) (leq-suc (n * 6) (n * 6) (leq-refl (n * 6)))
    ltM : T (lt (n * 6) M)
    ltM = subst (λ q → T (lt (n * 6) q)) (sym nCtx-eq) (leq-refl (n * 6))

  ctx-sc : All (λ A → T (scY K M A)) (ctx t)
  ctx-sc = All-++⁺ (levels-sc n M nM) (tyB-sc n M nM ∷ [])

  cgoal-sc : T (scY K M (cgoal t))
  cgoal-sc = tyU-sc n M nM

  objsFrom-sc : ∀ a j → T (leq (a + j) K) → T (scFs K (objsFrom a j))
  objsFrom-sc a zero    _ = tt
  objsFrom-sc a (suc j) p =
    ∧-intro (leq-trans (suc a) (a + suc j) K
               (subst (λ q → T (leq (suc a) q)) (sym (+-suc a j)) (leq-+ʳ (suc a) j)) p)
            (objsFrom-sc (suc a) j (subst (λ q → T (leq q K)) (+-suc a j) p))

  varsFrom-sc : ∀ a j → T (leq (a + j) M) → T (scTs K M (varsFrom a j))
  varsFrom-sc a zero    _ = tt
  varsFrom-sc a (suc j) p =
    ∧-intro (leq-trans (suc a) (a + suc j) M
               (subst (λ q → T (leq (suc a) q)) (sym (+-suc a j)) (leq-+ʳ (suc a) j)) p)
            (varsFrom-sc (suc a) j (subst (λ q → T (leq q M)) (+-suc a j) p))

  cterm-sc : T (scT K M (cterm t))
  cterm-sc = ∧-intro (objsFrom-sc 0 K (leq-refl K)) (varsFrom-sc 0 M (leq-refl M))

  egoal-sc : T (scY K M (egoal t))
  egoal-sc =
    ∧-intro (tyRU-sc n M nM)
      (∧-intro (rmap-sc ρ (cterm t) rs cterm-sc)
               (chain-sc n M (var (pos n 0)) nM ltM))

  goal-sc : ∀ e → T (scY K M (goal t e))
  goal-sc gc = cgoal-sc
  goal-sc gε = egoal-sc

------------------------------------------------------------------------
-- Lookup in a scoped list

All-lookup : ∀ {A : Set} {P : A → Set} xs i {x} → All P xs → lookup xs i ≡ just x → P x
All-lookup (x ∷ xs) zero    (p ∷ ps) refl = p
All-lookup (x ∷ xs) (suc i) (p ∷ ps) e    = All-lookup xs i ps e

------------------------------------------------------------------------
-- The identity instance of c is well typed in its own context

private
  T→≡′ : ∀ {b} → T b → b ≡ true
  T→≡′ {true} _ = refl

  if-true : ∀ {A : Set} {b} {x y : A} → T b → (if b then x else y) ≡ x
  if-true {b = true} _ = refl

lookup-++ʳ : ∀ {A : Set} (xs ys : List A) i → lookup (xs ++ ys) (length xs + i) ≡ lookup ys i
lookup-++ʳ []       ys i = refl
lookup-++ʳ (x ∷ xs) ys i = lookup-++ʳ xs ys i

module IdInst (t : Tmpl) (ok : T (okT t)) where
  open TmplScope t ok
  private
    K = nObj t
    M = nCtx t
    σ = instS (idφ t) (idts t)

  -- argsOk on a suffix Δ of ctx t starting at position a
  args-id : ∀ a Δ → (∀ i B → lookup Δ i ≡ just B → lookup (ctx t) (a + i) ≡ just B) →
            All (λ A → T (scY K M A)) Δ →
            T (argsOk (ctx t) σ (varsFrom a (length Δ)) Δ)
  args-id a []      h []       = tt
  args-id a (A ∷ Δ) h (p ∷ ps) = ∧-intro step (args-id (suc a) Δ h′ ps)
    where
    lk : lookup (ctx t) a ≡ just A
    lk = subst (λ q → lookup (ctx t) q ≡ just A) (+-zero a) (h 0 A refl)
    step : T (eqMaybeTy (infer (ctx t) (var a)) (sY σ A))
    step rewrite lk | inst-id K M A p = eqTy-refl A
    h′ : ∀ i B → lookup Δ i ≡ just B → lookup (ctx t) (suc a + i) ≡ just B
    h′ i B e = subst (λ q → lookup (ctx t) q ≡ just B) (+-suc a i) (h (suc i) B e)

  cterm-typed : infer (ctx t) (cterm t) ≡ just (cgoal t)
  cterm-typed =
    trans (if-true {b = okT t ∧ (length (idφ t) ==ℕ K) ∧ (length (idts t) ==ℕ M)
                         ∧ argsOk (ctx t) σ (idts t) (ctx t)}
             (∧-intro ok (∧-intro lenφ (∧-intro lents args))))
          (cong just (inst-id K M (cgoal t) cgoal-sc))
    where
    lenφ : T (length (idφ t) ==ℕ K)
    lenφ = subst (λ q → T (q ==ℕ K)) (sym (length-objsFrom 0 K)) (==ℕ-refl K)
    lents : T (length (idts t) ==ℕ M)
    lents = subst (λ q → T (q ==ℕ M)) (sym (length-varsFrom 0 M)) (==ℕ-refl M)
    args : T (argsOk (ctx t) σ (idts t) (ctx t))
    args = args-id 0 (ctx t) (λ i B e → e) ctx-sc
