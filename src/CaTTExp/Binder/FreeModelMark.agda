------------------------------------------------------------------------
-- One mark judgment for every kind of term (notes/unified-engine.md
-- §3, principle U2).
--
-- The binder kernel takes its mark judgment as a parameter
-- (CaTTExp.Binder.TypingWith) and needs three facts about it: MarkVar,
-- MarkRen and MarkSub. This module builds the judgment from four
-- pieces of data and proves the three facts once:
--
--   (VAR)  a variable has every mark entailed by a mark of its entry;
--   (CST)  a constant has the marks `cstHas` gives it;
--   (HEAD) a binder or head occurrence has the marks `headHas` gives
--          its former and selector (DES-inv, J2's UNI-inv, INIT's
--          invertible cells, LIFT's comparison, GB-cut's ε, T-fill);
--   (COH)  coh Δ A τ has mark m when `cohHas Δ A f m`, where f is the
--          marking of Δ pulled back along τ: f i m′ holds iff the i-th
--          entry of τ has mark m′.
--
-- (COH) is the general form of every propagation rule of spec
-- chapter 3: each of them reads only the head (Δ, A) and the marks of
-- the arguments. The one hypothesis needed for substitution is that
-- `cohHas` is monotone in the pulled-back marking. A rule given as a
-- positive Boolean formula in the argument marks is monotone by
-- construction (CaTTExp.Binder.FreeModelMarkPos), so every rule of
-- that shape inherits renaming, substitution and decidability.
--
-- Entailment `_⊑_` between marks (S36: trunc n ⊑ ord for n ≤ 1, …) is
-- a parameter; the judgment is upward closed under it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.FreeModelMark
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (_⊑_ : BM.Mark → BM.Mark → Bool)
  (cstHas  : Signature.K 𝕊 → BM.Mark → Bool)
  (headHas : Signature.B 𝕊 → Nat → BM.Mark → Bool)
  (cohHas  : Signature.Ctx 𝕊 → Signature.Ty 𝕊 →
             (Nat → BM.Mark → Bool) → BM.Mark → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B using (T∧; ∧T; lenₛ-∘)

------------------------------------------------------------------------
-- The judgment.

anyB : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
anyB p []       = false
anyB p (x ∷ xs) = p x ∨ anyB p xs

mutual
  markTm : Ctx → Mark → Tm → Bool
  markTm Γ m (var i)        = anyB (λ n → n ⊑ m) (marksAt Γ i)
  markTm Γ m (bvar _ _)     = false
  markTm Γ m (coh Δ A τ)    = cohHas Δ A (pull Γ τ) m
  markTm Γ m (cst k)        = cstHas k m
  markTm Γ m (bnd b y _ _)  = headHas b y m

  -- The marking of the head's context pulled back along τ. Out of
  -- range it is empty, so a typed τ (lenₛ τ = len Δ) gives exactly the
  -- marks of the entries of Δ.
  pull : Ctx → Sub → Nat → Mark → Bool
  pull Γ ⟨⟩       i m = false
  pull Γ (τ ,ₛ t) i m with i ==ℕ lenₛ τ
  ... | true  = markTm Γ m t
  ... | false = pull Γ τ i m

open import CaTTExp.Binder.TypingWith 𝕊 side markTm
open import CaTTExp.Binder.Rename 𝕊 side markTm using (_⊢ren_∶_; MarkRen; ==-transport)
open import CaTTExp.Binder.Subst 𝕊 side markTm using (MarkSub; MarkVar)
open _⊢ren_∶_

------------------------------------------------------------------------
-- Hypotheses.

-- Pointwise inclusion of markings.
_≤M_ : (Nat → Mark → Bool) → (Nat → Mark → Bool) → Set
f ≤M g = ∀ i m → T (f i m) → T (g i m)

record Hyp : Set where
  field
    ⊑-refl  : ∀ m → T (m ⊑ m)
    ⊑-trans : ∀ {l m n} → T (l ⊑ m) → T (m ⊑ n) → T (l ⊑ n)
    cst-up  : ∀ {k m n} → T (cstHas k m) → T (m ⊑ n) → T (cstHas k n)
    head-up : ∀ {b y m n} → T (headHas b y m) → T (m ⊑ n) → T (headHas b y n)
    coh-up  : ∀ {Δ A f m n} → T (cohHas Δ A f m) → T (m ⊑ n) → T (cohHas Δ A f n)
    -- The one structural hypothesis: more marks on the arguments never
    -- remove a mark from the coherence.
    coh-mono : ∀ {Δ A f g m} → f ≤M g → T (cohHas Δ A f m) → T (cohHas Δ A g m)

module Laws (h : Hyp) where
  open Hyp h

  private
    T∨ˡ : ∀ {a} b → T a → T (a ∨ b)
    T∨ˡ {true} b _ = tt

    T∨ʳ : ∀ a {b} → T b → T (a ∨ b)
    T∨ʳ true  _ = tt
    T∨ʳ false p = p


  -- any over a list is monotone in the predicate.
  any-mono : ∀ {A : Set} (p q : A → Bool) xs → (∀ x → T (p x) → T (q x)) →
             T (anyB p xs) → T (anyB q xs)
  any-mono p q (x ∷ xs) f r with p x in e
  ... | true  = T∨ˡ (anyB q xs) (f x (subst T (sym e) tt))
  ... | false = T∨ʳ (q x) (any-mono p q xs f r)

  -- Membership as a Boolean, and `any` picks up a member.
  memM : Mark → List Mark → Bool
  memM m []       = false
  memM m (n ∷ ns) = (m ==M n) ∨ memM m ns

  any-mem : ∀ (p : Mark → Bool) ns m → T (memM m ns) → T (p m) → T (anyB p ns)
  any-mem p (n ∷ ns) m q r with m ==M n in e
  ... | true  rewrite ==M-sound m n (subst T (sym e) tt) = T∨ˡ (anyB p ns) r
  ... | false = T∨ʳ (p n) (any-mem p ns m q r)

  ----------------------------------------------------------------------
  -- Upward closure under entailment.

  up : ∀ Γ t {m n} → T (markTm Γ m t) → T (m ⊑ n) → T (markTm Γ n t)
  up Γ (var i)       {m} {n} p q =
    any-mono (λ l → l ⊑ m) (λ l → l ⊑ n) (marksAt Γ i) (λ l r → ⊑-trans r q) p
  up Γ (bvar _ _)    () _
  up Γ (coh Δ A τ)   p q = coh-up p q
  up Γ (cst k)       p q = cst-up p q
  up Γ (bnd b y _ _) p q = head-up p q

  ----------------------------------------------------------------------
  -- (MARK): a variable has the marks of its entry.

  private
    all-self : ∀ (ns : List Mark) (ms : List Mark) →
               (∀ m → T (memM m ms) → T (memM m ns)) →
               T (all (λ m → anyB (λ n → n ⊑ m) ns) ms)
    all-self ns []       _ = tt
    all-self ns (m ∷ ms) inc =
      ∧T (any-mem (λ n → n ⊑ m) ns m (inc m (T∨ˡ (memM m ms) (==M-refl m))) (⊑-refl m))
         (all-self ns ms (λ l r → inc l (T∨ʳ (l ==M m) r)))

  markVar : MarkVar
  markVar {Γ} {i} _ _ = all-self (marksAt Γ i) (marksAt Γ i) (λ _ r → r)

  ----------------------------------------------------------------------
  -- Renaming and substitution, by one induction on typing.
  --
  -- The statement is generic in the map applied: θ is either a
  -- renaming or a substitution, and `onVar` says what it does to a
  -- marked variable. The coherence case is the same for both: the
  -- arguments' marks are carried by the induction hypothesis, and
  -- coh-mono lifts them to the coherence.

  private
    sub-len : ∀ {Δ σ Γ} → Δ ⊢sub σ ∶ Γ → lenₛ σ ≡ len Γ
    sub-len (⟨⟩-wf _)    = refl
    sub-len (,-wf s _ _) = cong suc (sub-len s)

    -- The marks a typed substitution owes the i-th entry.
    sub-marks : ∀ {Δ σ Γ i A} → Δ ⊢sub σ ∶ Γ → lookup Γ i ≡ just A →
                T (marksOK Δ (marksAt Γ i) (lookupₛ σ i))
    sub-marks {Γ = Γ ▸[ ms ] B} {i} (,-wf {σ} s _ o) eq with i ==ℕ len Γ in e
    ... | true  rewrite trans (==-transport i (sub-len s)) e = o
    ... | false rewrite trans (==-transport i (sub-len s)) e = sub-marks s eq

    all-get : ∀ (p : Mark → Bool) ms m → T (all p ms) → T (memM m ms) → T (p m)
    all-get p (n ∷ ns) m q r with m ==M n in e
    ... | true  rewrite ==M-sound m n (subst T (sym e) tt) = fst (T∧ {p n} q)
    ... | false = all-get p ns m (snd (T∧ {p n} q)) r

    any-get : ∀ (p : Mark → Bool) ns → T (anyB p ns) →
              Σ Mark λ n → T (p n) × T (memM n ns)
    any-get p (n ∷ ns) q with p n in e
    ... | true  = n , subst T (sym e) tt , T∨ˡ (memM n ns) (==M-refl n)
    ... | false = let (l , a , b) = any-get p ns q in l , a , T∨ʳ (l ==M n) b

  -- A map of contexts θ : Γ → Δ that respects marked variables.
  VarOK : Ctx → Ctx → Sub → Set
  VarOK Γ Δ θ = ∀ {i A m} → lookup Γ i ≡ just A → T (markTm Γ m (var i)) →
                T (markTm Δ m (lookupₛ θ i))

  mutual
    mark-map : ∀ {Γ Δ θ t A m} → VarOK Γ Δ θ → Γ ⊢tm t ∶ A →
               T (markTm Γ m t) → T (markTm Δ m (t [ θ ]tm))
    mark-map ok (var-wf _ eq) p = ok eq p
    mark-map {Γ} {Δ} {θ} {m = m} ok (coh-wf {Δ = Θ} {σ = τ} _ _ _ _ s) p =
      coh-mono (pull-map ok s) p
    mark-map ok (cst-wf _ _) p = p
    mark-map ok (bnd-wf _ _ _ _ _) p = p

    -- The pulled-back marking only grows along θ.
    pull-map : ∀ {Γ Δ θ τ Θ} → VarOK Γ Δ θ → Γ ⊢sub τ ∶ Θ →
               pull Γ τ ≤M pull Δ (τ ∘ θ)
    pull-map ok (⟨⟩-wf _) i m ()
    pull-map {θ = θ} ok (,-wf {τ} s d _) i m p
      rewrite lenₛ-∘ τ θ with i ==ℕ lenₛ τ
    ... | true  = mark-map ok d p
    ... | false = pull-map ok s i m p

  markRen : MarkRen
  markRen {Γ} {Γ′} {ρ} r d p = mark-map ok d p
    where
      ok : VarOK Γ Γ′ ρ
      ok {i} {m = m} eq q with look r i eq
      ... | j , ej , _ , mj rewrite ej | mj = q

  markSub : MarkSub
  markSub {Γ} {Δ} {σ} s d p = mark-map ok d p
    where
      ok : VarOK Γ Δ σ
      ok {i} {m = m} eq q =
        let (n , n⊑m , mem) = any-get (λ l → l ⊑ m) (marksAt Γ i) q in
        up Δ (lookupₛ σ i)
           (all-get (λ l → markTm Δ l (lookupₛ σ i)) (marksAt Γ i) n (sub-marks s eq) mem)
           n⊑m
