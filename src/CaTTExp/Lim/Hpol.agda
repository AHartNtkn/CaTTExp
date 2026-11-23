{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- The fast path Γ ⊢hpol (spec §4.4, above the kernel; design-decisions
-- §2.7, ledger B25, conservativity obligations B26): a decidable class
-- of named contexts whose free strict ω-category agrees with the free
-- weak one. No kernel rule mentions it; it only lets a checker present
-- a weight over the base itself instead of a resolution.
--
-- First base rule (this module): POSITIVE PATH 2-POLYGRAPHS, specified
-- inductively by `PosPath2` below:
--   * object variables  x : ⋆;
--   * 1-cells  f : x → y  between earlier object variables;
--   * 2-cells  α : s ⇒ t  where s and t are NONEMPTY composites (binary
--     `comp` trees, any bracketing) of earlier 1-cell variables with the
--     endpoints of α's boundary;
--   * every bound name fresh.
--
-- The decision procedure `hpolC` returns a `PosPath2` derivation or
-- nothing, so `hpol-sound` (the test accepts Γ ⟹ Γ is in the class) is
-- by construction, and `hpol-complete` proves the converse: the test
-- selects exactly the class.
--
-- Conservativity obligation for this rule (spec §4.4): PosPath2 Γ ⟹
-- F(Γ) ≃ Free(Γ). OPEN; plan in notes/hpol-obligations.md. Until it is
-- formalized this rule is not part of the fast path.
------------------------------------------------------------------------
module CaTTExp.Lim.Hpol where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Terms

------------------------------------------------------------------------
-- Specification.

-- A nonempty path of 1-cell variables from a to c.
data IsPath (Γ : NCtx) : Tm → Name → Name → Set where
  pvar  : ∀ {f a b} → typeOf Γ f ≡ just (arr ⋆ (var a) (var b)) →
          IsPath Γ (var f) a b
  pcomp : ∀ {p q a b c} → IsPath Γ p a b → IsPath Γ q b c →
          IsPath Γ (comp (var a) (var b) p (var c) q) a c

infix 4 _∉_
data _∉_ (n : Name) : NCtx → Set where
  ∉∅ : n ∉ ∅
  ∉▹ : ∀ {Γ x A} → n ∉ Γ → ¬ (n ≡ x) → n ∉ (Γ ▹ x ∶ A)

IsObj : NCtx → Name → Set
IsObj Γ a = typeOf Γ a ≡ just ⋆

-- The admissible types of a new entry.
data Entry (Γ : NCtx) : Ty → Set where
  eObj  : Entry Γ ⋆
  eEdge : ∀ {a b} → IsObj Γ a → IsObj Γ b → Entry Γ (arr ⋆ (var a) (var b))
  eCell : ∀ {a b s t} → IsObj Γ a → IsObj Γ b →
          IsPath Γ s a b → IsPath Γ t a b →
          Entry Γ (arr (arr ⋆ (var a) (var b)) s t)

data PosPath2 : NCtx → Set where
  pp∅ : PosPath2 ∅
  pp▹ : ∀ {Γ x A} → PosPath2 Γ → x ∉ Γ → Entry Γ A → PosPath2 (Γ ▹ x ∶ A)

------------------------------------------------------------------------
-- The decision procedure, returning derivations.

private
  ≢-from : ∀ m n → T (not (m ==ℕ n)) → ¬ (m ≡ n)
  ≢-from zero    zero    () refl
  ≢-from (suc m) (suc m′) p refl = ≢-from m m p refl

  ≡-from : ∀ {m n} → T (m ==ℕ n) → m ≡ n
  ≡-from {m} {n} = ==ℕ-sound m n

  mkComp : ∀ {Γ Γc Ac x y z p q a b b′ c} →
           Γc ≡ PComp → Ac ≡ arr ⋆ (var 0) (var 3) →
           a ≡ x → b ≡ y → b′ ≡ y → c ≡ z →
           IsPath Γ p a b → IsPath Γ q b′ c →
           IsPath Γ (coh Γc Ac (((((⟨⟩ ,ₛ var x) ,ₛ var y) ,ₛ p) ,ₛ var z) ,ₛ q)) x z
  mkComp refl refl refl refl refl refl dp dq = pcomp dp dq

  retarget : ∀ {Γ s a b a′ b′} → a′ ≡ a → b′ ≡ b → IsPath Γ s a′ b′ → IsPath Γ s a b
  retarget refl refl d = d

PathEv : NCtx → Tm → Set
PathEv Γ t = Σ Name λ a → Σ Name λ c → IsPath Γ t a c

pathVar : (Γ : NCtx) (f : Name) (m : Maybe Ty) → typeOf Γ f ≡ m → Maybe (PathEv Γ (var f))
pathVar Γ f (just (arr ⋆ (var a) (var b))) e = just (a , b , pvar e)
pathVar Γ f _ _ = nothing

pathC : (Γ : NCtx) (t : Tm) → Maybe (PathEv Γ t)
pathC Γ (var f) = pathVar Γ f (typeOf Γ f) refl
pathC Γ (coh Γc Ac (((((⟨⟩ ,ₛ var x) ,ₛ var y) ,ₛ p) ,ₛ var z) ,ₛ q)) =
  guard (Γc ==Ctx PComp) λ e₁ →
  guard (Ac ==Ty arr ⋆ (var 0) (var 3)) λ e₂ →
  pathC Γ p >>= λ { (a , b , dp) →
  pathC Γ q >>= λ { (b′ , c , dq) →
  guard (a ==ℕ x) λ e₃ → guard (b ==ℕ y) λ e₄ →
  guard (b′ ==ℕ y) λ e₅ → guard (c ==ℕ z) λ e₆ →
  just (x , z , mkComp (==Ctx-sound _ _ e₁) (==Ty-sound _ _ e₂)
                       (≡-from e₃) (≡-from e₄) (≡-from e₅) (≡-from e₆) dp dq) } }
pathC Γ _ = nothing

objGo : (Γ : NCtx) (a : Name) (m : Maybe Ty) → typeOf Γ a ≡ m → Maybe (IsObj Γ a)
objGo Γ a (just ⋆) e = just e
objGo Γ a _ _        = nothing

objC : (Γ : NCtx) (a : Name) → Maybe (IsObj Γ a)
objC Γ a = objGo Γ a (typeOf Γ a) refl

freshC : (Γ : NCtx) (n : Name) → Maybe (n ∉ Γ)
freshC ∅           n = just ∉∅
freshC (Γ ▹ x ∶ A) n =
  guard (not (n ==ℕ x)) λ ne → freshC Γ n >>= λ d → just (∉▹ d (≢-from n x ne))

entryC : (Γ : NCtx) (A : Ty) → Maybe (Entry Γ A)
entryC Γ ⋆ = just eObj
entryC Γ (arr ⋆ (var a) (var b)) =
  objC Γ a >>= λ oa → objC Γ b >>= λ ob → just (eEdge oa ob)
entryC Γ (arr (arr ⋆ (var a) (var b)) s t) =
  objC Γ a >>= λ oa → objC Γ b >>= λ ob →
  pathC Γ s >>= λ { (a₁ , b₁ , ds) →
  pathC Γ t >>= λ { (a₂ , b₂ , dt) →
  guard (a₁ ==ℕ a) λ e₁ → guard (b₁ ==ℕ b) λ e₂ →
  guard (a₂ ==ℕ a) λ e₃ → guard (b₂ ==ℕ b) λ e₄ →
  just (eCell oa ob (retarget (≡-from e₁) (≡-from e₂) ds)
                    (retarget (≡-from e₃) (≡-from e₄) dt)) } }
entryC Γ _ = nothing

hpolC : (Γ : NCtx) → Maybe (PosPath2 Γ)
hpolC ∅           = just pp∅
hpolC (Γ ▹ x ∶ A) =
  hpolC Γ >>= λ d → freshC Γ x >>= λ f → entryC Γ A >>= λ e → just (pp▹ d f e)

hpol? : NCtx → Bool
hpol? Γ = is-just (hpolC Γ)

-- The judgement Γ ⊢hpol (first base rule).
_⊢hpol : NCtx → Set
Γ ⊢hpol = T (hpol? Γ)

-- Soundness: the test accepts only positive path 2-polygraphs.
hpol-sound : ∀ Γ → Γ ⊢hpol → PosPath2 Γ
hpol-sound Γ p = from-just (hpolC Γ) {p}

------------------------------------------------------------------------
-- Completeness: every positive path 2-polygraph passes the test, so the
-- test selects exactly the class PosPath2.

private
  bind-just : ∀ {A B : Set} {m : Maybe A} {f : A → Maybe B} →
              T (is-just m) → (∀ x → m ≡ just x → T (is-just (f x))) →
              T (is-just (m >>= f))
  bind-just {m = just x} _ k = k x refl

  guard-just : ∀ {A : Set} {b : Bool} {k : T b → Maybe A} →
               T b → (∀ p → T (is-just (k p))) → T (is-just (guard b k))
  guard-just {b = true} p k = k p

  eqT : ∀ {m n} → m ≡ n → T (m ==ℕ n)
  eqT {m} refl = ==ℕ-refl m

  neqT : ∀ m n → ¬ (m ≡ n) → T (not (m ==ℕ n))
  neqT zero    zero    ne = ne refl
  neqT zero    (suc n) ne = tt
  neqT (suc m) zero    ne = tt
  neqT (suc m) (suc n) ne = neqT m n (λ e → ne (cong suc e))

-- The endpoints of a path are determined by the term.
ends-unique : ∀ {Γ t a c a′ c′} → IsPath Γ t a c → IsPath Γ t a′ c′ → (a ≡ a′) × (c ≡ c′)
ends-unique (pvar e) (pvar e′) with trans (sym e) e′
... | refl = refl , refl
ends-unique (pcomp _ _) (pcomp _ _) = refl , refl

private
  pathVar-just : ∀ Γ f m (e : typeOf Γ f ≡ m) {a b} →
                 m ≡ just (arr ⋆ (var a) (var b)) → T (is-just (pathVar Γ f m e))
  pathVar-just Γ f .(just (arr ⋆ (var _) (var _))) e refl = tt

  objGo-just : ∀ Γ a m (e : typeOf Γ a ≡ m) → m ≡ just ⋆ → T (is-just (objGo Γ a m e))
  objGo-just Γ a .(just ⋆) e refl = tt

pathC-complete : ∀ {Γ t a c} → IsPath Γ t a c → T (is-just (pathC Γ t))
pathC-complete {Γ} {var f} (pvar e) = pathVar-just Γ f (typeOf Γ f) refl e
pathC-complete {Γ} (pcomp {p} {q} {a} {b} {c} dp dq) =
  guard-just {b = PComp ==Ctx PComp} tt λ _ →
  guard-just {b = arr ⋆ (var 0) (var 3) ==Ty arr ⋆ (var 0) (var 3)} tt λ _ →
  bind-just {m = pathC Γ p} (pathC-complete dp) λ { (a₁ , b₁ , dp₁) _ →
  bind-just {m = pathC Γ q} (pathC-complete dq) λ { (b₂ , c₂ , dq₂) _ →
  guard-just (eqT (fst (ends-unique dp₁ dp))) λ _ →
  guard-just (eqT (snd (ends-unique dp₁ dp))) λ _ →
  guard-just (eqT (fst (ends-unique dq₂ dq))) λ _ →
  guard-just (eqT (snd (ends-unique dq₂ dq))) λ _ → tt } }

objC-complete : ∀ {Γ a} → IsObj Γ a → T (is-just (objC Γ a))
objC-complete {Γ} {a} e = objGo-just Γ a (typeOf Γ a) refl e

freshC-complete : ∀ {Γ n} → n ∉ Γ → T (is-just (freshC Γ n))
freshC-complete ∉∅ = tt
freshC-complete {Γ ▹ x ∶ A} {n} (∉▹ d ne) =
  guard-just (neqT n x ne) λ _ → bind-just {m = freshC Γ n} (freshC-complete d) λ _ _ → tt

entryC-complete : ∀ {Γ A} → Entry Γ A → T (is-just (entryC Γ A))
entryC-complete eObj = tt
entryC-complete {Γ} (eEdge {a} {b} oa ob) =
  bind-just {m = objC Γ a} (objC-complete oa) λ _ _ →
  bind-just {m = objC Γ b} (objC-complete ob) λ _ _ → tt
entryC-complete {Γ} (eCell {a} {b} {s} {t} oa ob ds dt) =
  bind-just {m = objC Γ a} (objC-complete oa) λ _ _ →
  bind-just {m = objC Γ b} (objC-complete ob) λ _ _ →
  bind-just {m = pathC Γ s} (pathC-complete ds) λ { (a₁ , b₁ , ds₁) _ →
  bind-just {m = pathC Γ t} (pathC-complete dt) λ { (a₂ , b₂ , dt₁) _ →
  guard-just (eqT (fst (ends-unique ds₁ ds))) λ _ →
  guard-just (eqT (snd (ends-unique ds₁ ds))) λ _ →
  guard-just (eqT (fst (ends-unique dt₁ dt))) λ _ →
  guard-just (eqT (snd (ends-unique dt₁ dt))) λ _ → tt } }

hpol-complete : ∀ {Γ} → PosPath2 Γ → Γ ⊢hpol
hpol-complete pp∅ = tt
hpol-complete (pp▹ {Γ} {x} {A} d f e) =
  bind-just {m = hpolC Γ} (hpol-complete d) λ _ _ →
  bind-just {m = freshC Γ x} (freshC-complete f) λ _ _ →
  bind-just {m = entryC Γ A} (entryC-complete e) λ _ _ → tt

------------------------------------------------------------------------
-- Examples.

private
  v : Nat → Tm
  v = var

  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

-- Parallel pair x ⇉ y (equalizers): a graph.
Γpair : NCtx
Γpair = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (0 ⇒⋆ 1)

pair-hpol : Γpair ⊢hpol
pair-hpol = tt

-- x, a : x → x, μ : a · a ⇒ a.
Γmu : NCtx
Γmu = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)
        ▹ 2 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 0) (v 1) (v 0) (v 1)) (v 1)

mu-hpol : Γmu ⊢hpol
mu-hpol = tt

-- The bubble x, σ : 1_x ⇒ 1_x is not in the class.
Γbub : NCtx
Γbub = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ arr (0 ⇒⋆ 0) (idc (v 0)) (idc (v 0))

bubble-not-hpol : hpol? Γbub ≡ false
bubble-not-hpol = refl

-- A 2-cell between paths with mismatched endpoints is rejected.
Γbad : NCtx
Γbad = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (1 ⇒⋆ 0)
         ▹ 4 ∶ arr (0 ⇒⋆ 1) (v 2) (v 3)

bad-not-hpol : hpol? Γbad ≡ false
bad-not-hpol = refl

-- Shadowing is rejected (independent review counterexample).
Γsh : NCtx
Γsh = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (1 ⇒⋆ 0) ▹ 1 ∶ (0 ⇒⋆ 0)
        ▹ 4 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 1) (v 2) (v 0) (v 3)) (v 1)

sh-not-hpol : hpol? Γsh ≡ false
sh-not-hpol = refl

-- Reusing a name (here a loop that rebinds its own vertex name 0) is
-- rejected; genuine self-loops such as Γmu are accepted.
selfloop-not-hpol : hpol? (∅ ▹ 0 ∶ ⋆ ▹ 0 ∶ (0 ⇒⋆ 0)) ≡ false
selfloop-not-hpol = refl

-- Composites of length 2 on both sides: x, f g h k : x → x,
-- β : f · g ⇒ h · k.
Γsq : NCtx
Γsq = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0) ▹ 2 ∶ (0 ⇒⋆ 0) ▹ 3 ∶ (0 ⇒⋆ 0) ▹ 4 ∶ (0 ⇒⋆ 0)
        ▹ 5 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 0) (v 1) (v 0) (v 2))
                           (comp (v 0) (v 0) (v 3) (v 0) (v 4))

sq-hpol : Γsq ⊢hpol
sq-hpol = tt

-- An identity on one side only is rejected.
oneid-not-hpol : hpol? (∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)
                          ▹ 2 ∶ arr (0 ⇒⋆ 0) (v 1) (idc (v 0))) ≡ false
oneid-not-hpol = refl
