------------------------------------------------------------------------
-- Naturality cylinders are well typed (Conjecture N, ledger C1), in
-- every dimension, relative to a typed filler family.
--
--   cyl-wf : ValidD D Γ Δ → Γ ⊢tm t ∶ A → AllGood t → T (touched D t) →
--            Δ ⊢tm cyl D t ∶ cylTy D t A
--
-- i.e. t↑ : a_t → b_t for every term t of every context Γ, given
--
--   * a valid cylinder datum D on Γ into Δ (`ValidD`): typed copies
--     mm, mp : Δ → Γ; for each selected variable x a cell
--     th x : a_x → b_x; unselected variables have equal copies, and
--     the selection is up-closed;
--   * a filler family K that is scoped (`Scoped`) and well typed on
--     every pasting coherence the term uses (`FillerOK Good K`): for
--     Q ⊢ps, B full over Q, Y a nonempty up-closed selection with
--     Good Q B, the term K Q B Y has type a_c → b_c in the cylinder
--     context Q↑Y, where c = coh Q B id.
--
-- `Good` grades the result: with Good Q B = ⊤ the statement covers
-- every term. CaTTExp.Naturality.DimOne constructs a filler family K₁
-- with FillerOK K₁ Dim1 (every coherence of dimension 1), and derives
-- the cylinder of every term of dimension ≤ 1 for every valid datum
-- (`cyl₁-wf`). CaTTExp.Naturality.General constructs a family Kω for
-- every dimension, with FillerOK Kω Good, where Good is CONDITIONAL in
-- dimension ≥ 2 on rcS answering the cylinder query (RCq, ledger C1d
-- item (2)); no unconditional filler of dimension ≥ 2 exists yet.
--
-- The proof is by structural induction on the typing derivation of t.
-- At t = coh Q B γ the filler's type is transported along γ↑ with the
-- commutation laws of CaTTExp.Naturality.Commute:
--
--   (a_c → b_c)[γ↑]  =  cylTy ((gen Y)[γ↑]) c B      (cylTy-sub)
--                    =  cylTy (pre γ D) c B          (cylTy-ext)
--                    =  cylTy D (c[γ]) (B[γ])        (cylTy-pre)
--
-- and γ↑ : Δ → Q↑Y is typed entry by entry, using the induction
-- hypothesis at the arguments of γ.
------------------------------------------------------------------------
module CaTTExp.Naturality.Typing where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn; ≡-T) renaming (<→≢ to <→≢')
open import CaTTExp.Derived using (idS; id-wf; lk-ext; lk-top)
open import CaTTExp.DerivedBoundary using (idS∘)
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Commute

------------------------------------------------------------------------
-- Hypotheses.

-- Y is up-closed over Q: an unselected variable's type uses no
-- selected variable.
UpSel : Ctx → Sel → Set
UpSel Q Y = ∀ q A → lookup Q q ≡ just A → selAt Y q ≡ false → anyL (selAt Y) (fvTy A) ≡ false

module Hyp (K : Filler) where
  open Cyl K

  -- The filler family is well typed on the pasting coherences that
  -- satisfy Good.
  FillerOK : (Ctx → Ty → Set) → Set
  FillerOK Good =
    ∀ {Q A s u Y} → Q ⊢ps → Q ⊢ctx → Q ⊢ty arr A s u → T (cattSide Q A s u) →
    lenSel Y ≡ len Q → UpSel Q Y → T (anySel Y) → Good Q (arr A s u) →
    cylCtx Q Y ⊢tm K Q (arr A s u) Y ∶ cylTy (gen Y) (cohId Q (arr A s u)) (arr A s u)

  -- A valid cylinder datum on Γ, landing in Δ (`ValidD`).
  record ValidD (D : Datum) (Γ Δ : Ctx) : Set where
    field
      vmm   : Δ ⊢sub mm D ∶ Γ
      vmp   : Δ ⊢sub mp D ∶ Γ
      vth   : ∀ x A → lookup Γ x ≡ just A → T (sel D x) → Δ ⊢tm th D x ∶ cylTy D (var x) A
      vsame : ∀ x → T (x <ℕ len Γ) → sel D x ≡ false → lookupₛ (mm D) x ≡ lookupₛ (mp D) x
      vup   : ∀ x A → lookup Γ x ≡ just A → sel D x ≡ false → anyL (sel D) (fvTy A) ≡ false

  -- Every coherence occurring in t (through arguments) is Good.
  module _ (Good : Ctx → Ty → Set) where
    mutual
      AllGood : Tm → Set
      AllGood (var x)     = ⊤
      AllGood (coh Q B γ) = Good Q B × AllGoodS γ
      AllGood (cst _)     = ⊤

      AllGoodS : Sub → Set
      AllGoodS ⟨⟩       = ⊤
      AllGoodS (γ ,ₛ t) = AllGoodS γ × AllGood t

------------------------------------------------------------------------
-- Small facts.

∨-false-l : ∀ {a b} → (a ∨ b) ≡ false → a ≡ false
∨-false-l {false} e = refl

∨-false-r : ∀ {a b} → (a ∨ b) ≡ false → b ≡ false
∨-false-r {false} e = e

T-∨-false : ∀ {a} → T (a ∨ false) → T a
T-∨-false {true} _ = tt

not-T : ∀ {b} → (T b → ⊥) → b ≡ false
not-T {true}  f = ⊥-elim (f tt)
not-T {false} f = refl

anyL-false : ∀ xs → anyL (λ _ → false) xs ≡ false
anyL-false []       = refl
anyL-false (x ∷ xs) = anyL-false xs

lt-lt : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
lt-lt = <-suc

le-refl : ∀ n → T (n <ℕ suc n)
le-refl = n<sn

le-suc : ∀ n → T (n <ℕ suc (suc n))
le-suc n = <-suc n (suc n) (n<sn n)

le-suc2 : ∀ n → T (n <ℕ suc (suc (suc n)))
le-suc2 n = <-suc n _ (le-suc n)

le-add : ∀ n k → T (n <ℕ suc (k + n))
le-add n zero    = n<sn n
le-add n (suc k) = <-suc n _ (le-add n k)

lk-1 : ∀ ρ a → lookupₛ (ρ ,ₛ a) (lenₛ ρ) ≡ a
lk-1 = lk-top

lk-2 : ∀ ρ a b → lookupₛ (ρ ,ₛ a ,ₛ b) (suc (lenₛ ρ)) ≡ b
lk-2 ρ a b = lk-top (ρ ,ₛ a) b

lk-3 : ∀ ρ a b c → lookupₛ (ρ ,ₛ a ,ₛ b ,ₛ c) (suc (suc (lenₛ ρ))) ≡ c
lk-3 ρ a b c = lk-top (ρ ,ₛ a ,ₛ b) c

lk-1of3 : ∀ ρ a b c → lookupₛ (ρ ,ₛ a ,ₛ b ,ₛ c) (lenₛ ρ) ≡ a
lk-1of3 ρ a b c =
  trans (lk-ext (ρ ,ₛ a ,ₛ b) c (lenₛ ρ) (le-suc (lenₛ ρ)))
  (trans (lk-ext (ρ ,ₛ a) b (lenₛ ρ) (n<sn (lenₛ ρ))) (lk-top ρ a))

lk-2of3 : ∀ ρ a b c → lookupₛ (ρ ,ₛ a ,ₛ b ,ₛ c) (suc (lenₛ ρ)) ≡ b
lk-2of3 ρ a b c = trans (lk-ext (ρ ,ₛ a ,ₛ b) c (suc (lenₛ ρ)) (n<sn (suc (lenₛ ρ)))) (lk-top (ρ ,ₛ a) b)

-- Scoping is monotone.
mutual
  sc-mono-tm : ∀ {m n} t → T (m <ℕ suc n) → ScTm m t → ScTm n t
  sc-mono-tm {m} {n} (var i)     p q = <-≤ i m n q p
  sc-mono-tm         (coh Q B γ) p q = sc-mono-sub γ p q
  sc-mono-tm         (cst _)     p q = tt

  sc-mono-sub : ∀ {m n} γ → T (m <ℕ suc n) → ScSub m γ → ScSub n γ
  sc-mono-sub ⟨⟩       p q       = tt
  sc-mono-sub (γ ,ₛ t) p (q , r) = sc-mono-sub γ p q , sc-mono-tm t p r

  <-≤ : ∀ i m n → T (i <ℕ m) → T (m <ℕ suc n) → T (i <ℕ n)
  <-≤ zero    (suc m) (suc n) _ _ = tt
  <-≤ (suc i) (suc m) (suc n) p q = <-≤ i m n p q
  <-≤ zero    (suc m) zero    _ ()
  <-≤ (suc i) (suc m) zero    _ ()

sc-mono-ty : ∀ {m n} A → T (m <ℕ suc n) → ScTy m A → ScTy n A
sc-mono-ty ⋆           p q           = tt
sc-mono-ty (arr A t u) p (a , b , c) = sc-mono-ty A p a , sc-mono-tm t p b , sc-mono-tm u p c

------------------------------------------------------------------------
-- Selections, generic data and γ↑, syntactically.

module Gen (K : Filler) where
  open Cyl K
  open Laws K

  len-genMm : ∀ Y → lenₛ (genMm Y) ≡ lenSel Y
  len-genMm ◇       = refl
  len-genMm (Y ◂ b) = cong suc (len-genMm Y)

  len-genMp : ∀ Y → lenₛ (genMp Y) ≡ lenSel Y
  len-genMp ◇           = refl
  len-genMp (Y ◂ true)  = cong suc (len-genMp Y)
  len-genMp (Y ◂ false) = cong suc (len-genMp Y)

  len-genTh : ∀ Y → lenₛ (genTh Y) ≡ lenSel Y
  len-genTh ◇       = refl
  len-genTh (Y ◂ b) = cong suc (len-genTh Y)

  cnt-mono : ∀ Y b → T (cnt Y <ℕ suc (cnt (Y ◂ b)))
  cnt-mono Y true  = le-add (cnt Y) 3
  cnt-mono Y false = le-add (cnt Y) 1

  cnt-lt : ∀ Y b → T (cnt Y <ℕ cnt (Y ◂ b))
  cnt-lt Y true  = le-add (cnt Y) 2
  cnt-lt Y false = n<sn (cnt Y)

  sc-genMm : ∀ Y → ScSub (cnt Y) (genMm Y)
  sc-genMm ◇       = tt
  sc-genMm (Y ◂ b) = sc-mono-sub (genMm Y) (cnt-mono Y b) (sc-genMm Y) , cnt-lt Y b

  sc-genMp : ∀ Y → ScSub (cnt Y) (genMp Y)
  sc-genMp ◇           = tt
  sc-genMp (Y ◂ true)  = sc-mono-sub (genMp Y) (cnt-mono Y true) (sc-genMp Y) , le-suc (suc (cnt Y))
  sc-genMp (Y ◂ false) = sc-mono-sub (genMp Y) (cnt-mono Y false) (sc-genMp Y) , n<sn (cnt Y)

  -- The cylinder level of a selected variable is in scope.
  sc-genTh : ∀ Y i → T (i <ℕ lenSel Y) → T (selAt Y i) → ScTm (cnt Y) (lookupₛ (genTh Y) i)
  sc-genTh (Y ◂ true) i p q =
    subst (ScTm (cnt (Y ◂ true)))
      (sym (cong (λ m → if i ==ℕ m then var (suc (suc (cnt Y))) else lookupₛ (genTh Y) i) (len-genTh Y)))
      (go (i ==ℕ lenSel Y) refl q)
    where
    go : ∀ v → (i ==ℕ lenSel Y) ≡ v → T (if v then true else selAt Y i) →
         ScTm (cnt (Y ◂ true)) (if v then var (suc (suc (cnt Y))) else lookupₛ (genTh Y) i)
    go true  e _ = n<sn (suc (suc (cnt Y)))
    go false e q' =
      sc-mono-tm (lookupₛ (genTh Y) i) (cnt-mono Y true) (sc-genTh Y i (lt-ne i (lenSel Y) p e) q')
  sc-genTh (Y ◂ false) i p q =
    subst (ScTm (cnt (Y ◂ false)))
      (sym (cong (λ m → if i ==ℕ m then var (suc (suc (cnt Y))) else lookupₛ (genTh Y) i) (len-genTh Y)))
      (go (i ==ℕ lenSel Y) refl q)
    where
    go : ∀ v → (i ==ℕ lenSel Y) ≡ v → T (if v then false else selAt Y i) →
         ScTm (cnt (Y ◂ false)) (if v then var (suc (suc (cnt Y))) else lookupₛ (genTh Y) i)
    go true  e ()
    go false e q' =
      sc-mono-tm (lookupₛ (genTh Y) i) (cnt-mono Y false) (sc-genTh Y i (lt-ne i (lenSel Y) p e) q')

  lenSel-mask : ∀ D γ → lenSel (mask D γ) ≡ lenₛ γ
  lenSel-mask D ⟨⟩       = refl
  lenSel-mask D (γ ,ₛ t) = cong suc (lenSel-mask D γ)

  sel-mask : ∀ D γ i → T (i <ℕ lenₛ γ) → selAt (mask D γ) i ≡ touched D (lookupₛ γ i)
  sel-mask D (γ ,ₛ t) i p rewrite lenSel-mask D γ with i ==ℕ lenₛ γ in e
  ... | true  = refl
  ... | false = sel-mask D γ i (lt-ne i (lenₛ γ) p e)

  any-mask : ∀ D γ → anySel (mask D γ) ≡ anyL (sel D) (fvSub γ)
  any-mask D ⟨⟩       = refl
  any-mask D (γ ,ₛ t) = trans (cong (_∨ touched D t) (any-mask D γ)) (sym (anyL-++ (sel D) (fvSub γ) (fvTm t)))

  -- Extending a substitution by one entry of γ↑.
  liftOne-ext-tm : ∀ x ρ a b c v → ScTm (lenₛ ρ) x → x [ liftOne ρ a b c v ]tm ≡ x [ ρ ]tm
  liftOne-ext-tm x ρ a b c true  s =
    trans (Sb.ext-tm x (ρ ,ₛ a ,ₛ b) c (Sb.scTm-suc x (Sb.scTm-suc x s)))
    (trans (Sb.ext-tm x (ρ ,ₛ a) b (Sb.scTm-suc x s)) (Sb.ext-tm x ρ a s))
  liftOne-ext-tm x ρ a b c false s = Sb.ext-tm x ρ a s

  liftOne-ext-sub : ∀ τ ρ a b c v → ScSub (lenₛ ρ) τ → τ ∘ liftOne ρ a b c v ≡ τ ∘ ρ
  liftOne-ext-sub ⟨⟩       ρ a b c v _       = refl
  liftOne-ext-sub (τ ,ₛ x) ρ a b c v (p , q) =
    cong₂ _,ₛ_ (liftOne-ext-sub τ ρ a b c v p) (liftOne-ext-tm x ρ a b c v q)

  liftOne-lk0 : ∀ ρ a b c v → lookupₛ (liftOne ρ a b c v) (lenₛ ρ) ≡ a
  liftOne-lk0 ρ a b c true  = lk-1of3 ρ a b c
  liftOne-lk0 ρ a b c false = lk-1 ρ a

  sc-liftS-genMm : ∀ D γ → ScSub (lenₛ (liftS D γ)) (genMm (mask D γ))
  sc-liftS-genMm D γ = subst (λ m → ScSub m (genMm (mask D γ))) (sym (len-liftS D γ)) (sc-genMm (mask D γ))

  -- genMm Y ∘ γ↑ = γ ∘ mm.
  gm : ∀ D γ → genMm (mask D γ) ∘ liftS D γ ≡ γ ∘ mm D
  gm D ⟨⟩       = refl
  gm D (γ ,ₛ t) =
    cong₂ _,ₛ_
      (trans (liftOne-ext-sub (genMm (mask D γ)) (liftS D γ) a b c v (sc-liftS-genMm D γ)) (gm D γ))
      (trans (cong (lookupₛ (liftOne (liftS D γ) a b c v)) (sym (len-liftS D γ))) (liftOne-lk0 (liftS D γ) a b c v))
    where a = t [ mm D ]tm
          b = t [ mp D ]tm
          c = cyl D t
          v = touched D t

  -- genMp Y ∘ γ↑ = γ ∘ mp, when the untouched arguments have equal copies.
  SameU : Datum → Sub → Set
  SameU D ⟨⟩       = ⊤
  SameU D (γ ,ₛ t) = SameU D γ × (touched D t ≡ false → t [ mm D ]tm ≡ t [ mp D ]tm)

  gp : ∀ D γ → SameU D γ → genMp (mask D γ) ∘ liftS D γ ≡ γ ∘ mp D
  gp D ⟨⟩       _       = refl
  gp D (γ ,ₛ t) (h , h') with touched D t in e
  ... | true  =
    cong₂ _,ₛ_
      (trans (liftOne-ext-sub (genMp (mask D γ)) (liftS D γ) a b c true sc) (gp D γ h))
      (trans (cong (lookupₛ (liftS D γ ,ₛ a ,ₛ b ,ₛ c)) (sym (cong suc (len-liftS D γ)))) (lk-2of3 (liftS D γ) a b c))
    where a = t [ mm D ]tm
          b = t [ mp D ]tm
          c = cyl D t
          sc = subst (λ m → ScSub m (genMp (mask D γ))) (sym (len-liftS D γ)) (sc-genMp (mask D γ))
  ... | false =
    cong₂ _,ₛ_
      (trans (liftOne-ext-sub (genMp (mask D γ)) (liftS D γ) a b c false sc) (gp D γ h))
      (trans (cong (lookupₛ (liftS D γ ,ₛ a)) (sym (len-liftS D γ))) (trans (lk-1 (liftS D γ) a) (h' refl)))
    where a = t [ mm D ]tm
          b = t [ mp D ]tm
          c = cyl D t
          sc = subst (λ m → ScSub m (genMp (mask D γ))) (sym (len-liftS D γ)) (sc-genMp (mask D γ))

  -- (q↑)[γ↑] = cyl (γ q) for every selected q.
  gth : ∀ D γ i → T (i <ℕ lenₛ γ) → T (selAt (mask D γ) i) →
        lookupₛ (genTh (mask D γ)) i [ liftS D γ ]tm ≡ cyl D (lookupₛ γ i)
  gth D (γ ,ₛ t) i p q with i ==ℕ lenₛ γ in e
  ... | true = go (touched D t) refl q
    where
    lY : lenₛ (genTh (mask D γ)) ≡ lenₛ γ
    lY = trans (len-genTh (mask D γ)) (lenSel-mask D γ)
    e' : (i ==ℕ lenₛ (genTh (mask D γ))) ≡ true
    e' = trans (cong (i ==ℕ_) lY) e
    go : ∀ v → touched D t ≡ v → T (selAt (mask D γ ◂ v) i) →
         lookupₛ (genTh (mask D γ ◂ v)) i [ liftOne (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) v ]tm ≡ cyl D t
    go true  _ _ rewrite e' =
      trans (cong (lookupₛ (liftS D γ ,ₛ t [ mm D ]tm ,ₛ t [ mp D ]tm ,ₛ cyl D t))
                  (cong (λ m → suc (suc m)) (sym (len-liftS D γ))))
            (lk-3 (liftS D γ) _ _ _)
    go false _ q' rewrite trans (cong (i ==ℕ_) (lenSel-mask D γ)) e = ⊥-elim q'
  ... | false =
    trans (cong (_[ liftS D (γ ,ₛ t) ]tm) lkY)
    (trans (liftOne-ext-tm x (liftS D γ) (t [ mm D ]tm) (t [ mp D ]tm) (cyl D t) (touched D t)
              (subst (λ m → ScTm m x) (sym (len-liftS D γ))
                 (sc-genTh (mask D γ) i (subst (λ m → T (i <ℕ m)) (sym (lenSel-mask D γ)) p') q')))
           (gth D γ i p' q'))
    where
    p' = lt-ne i (lenₛ γ) p e
    x = lookupₛ (genTh (mask D γ)) i
    lY : lenₛ (genTh (mask D γ)) ≡ lenₛ γ
    lY = trans (len-genTh (mask D γ)) (lenSel-mask D γ)
    lkY : lookupₛ (genTh (mask D (γ ,ₛ t))) i ≡ x
    lkY = lk-ext (genTh (mask D γ)) _ i (subst (λ m → T (i <ℕ m)) (sym lY) p')
    q' : T (selAt (mask D γ) i)
    q' = subst T (trans (cong (λ m → if i ==ℕ m then touched D t else selAt (mask D γ) i) (lenSel-mask D γ))
                        (if-f e)) q

------------------------------------------------------------------------
-- The theorem.

lk-untouched : ∀ f γ i → anyL f (fvSub γ) ≡ false → T (i <ℕ lenₛ γ) → anyL f (fvTm (lookupₛ γ i)) ≡ false
lk-untouched f (γ ,ₛ t) i e p with i ==ℕ lenₛ γ in q
... | true  = ∨-false-r (trans (sym (anyL-++ f (fvSub γ) (fvTm t))) e)
... | false = lk-untouched f γ i (∨-false-l (trans (sym (anyL-++ f (fvSub γ) (fvTm t))) e)) (lt-ne i (lenₛ γ) p q)

module Main (K : Filler) (Ksc : Scoped K) (Good : Ctx → Ty → Set) (ok : Hyp.FillerOK K Good) where
  open Cyl K
  open Laws K
  open Post Ksc
  open Gen K
  open Hyp K

  module _ {D : Datum} {Γ Δ : Ctx} (V : ValidD D Γ Δ) where
    open ValidD V

    private
      wΔ : Δ ⊢ctx
      wΔ = Sb.sub-ctx closed vmm

    mutual
      same-tm : ∀ t → ScTm (len Γ) t → touched D t ≡ false → t [ mm D ]tm ≡ t [ mp D ]tm
      same-tm (var x)     p e = vsame x p (∨-false-l e)
      same-tm (coh Q B γ) p e = cong (coh Q B) (same-sub γ p e)
      same-tm (cst ())    p e

      same-sub : ∀ γ → ScSub (len Γ) γ → anyL (sel D) (fvSub γ) ≡ false → γ ∘ mm D ≡ γ ∘ mp D
      same-sub ⟨⟩       p       e = refl
      same-sub (γ ,ₛ t) (p , q) e =
        cong₂ _,ₛ_ (same-sub γ p (∨-false-l e')) (same-tm t q (∨-false-r e'))
        where e' = trans (sym (anyL-++ (sel D) (fvSub γ) (fvTm t))) e

    sameU : ∀ γ → ScSub (len Γ) γ → SameU D γ
    sameU ⟨⟩       _       = tt
    sameU (γ ,ₛ t) (p , q) = sameU γ p , same-tm t q

    -- An untouched term has an untouched type.
    UT : ∀ {t A} → Γ ⊢tm t ∶ A → touched D t ≡ false → anyL (sel D) (fvTy A) ≡ false
    UT (var-wf {i} {A} w eq) e = vup i A eq (∨-false-l e)
    UT (coh-wf {Δ = Q} {A'} {s} {u} {γ} pQ wQ wB side sγ) e =
      trans (anyL-ty (sel D) γ (arr A' s u))
      (trans (anyL-ext-ty (img (sel D) γ) (λ _ → false) (λ i q → lk-untouched (sel D) γ i e q) (arr A' s u) scB)
             (anyL-false (fvTy (arr A' s u))))
      where scB = subst (λ m → ScTy m (arr A' s u)) (sym (snd (Sb.sub-sc closed sγ))) (Sb.ty-sc closed wB)
    UT (cst-wf {()} _ _) e

    -- The selection of γ↑ is up-closed.
    mask-up : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Q ⊢ctx → UpSel Q (mask D γ)
    mask-up {γ} {Q} sγ wQ q A eq e =
      trans (anyL-ext-ty (selAt (mask D γ)) (img (sel D) γ) (λ i r → sel-mask D γ i r) A scA')
      (trans (sym (anyL-ty (sel D) γ A))
             (UT (Sb.lookup-sub closed wQ eq sγ) (trans (sym (sel-mask D γ q ql')) e)))
      where
      lγ = snd (Sb.sub-sc closed sγ)
      cl = Sb.ctx-lookup closed wQ eq
      ql' : T (q <ℕ lenₛ γ)
      ql' = subst (λ m → T (q <ℕ m)) (sym lγ) (fst cl)
      scA' : ScTy (lenₛ γ) A
      scA' = subst (λ m → ScTy m A) (sym lγ) (snd cl)

    mutual
      cyl-wf : ∀ {t A} → Γ ⊢tm t ∶ A → AllGood Good t → T (touched D t) → Δ ⊢tm cyl D t ∶ cylTy D t A
      cyl-wf (var-wf {i} {A} w eq) g p = vth i A eq (T-∨-false p)
      cyl-wf (coh-wf {Δ = Q} {A'} {s} {u} {γ} pQ wQ wB side sγ) (gQ , gγ) p =
        subst (Δ ⊢tm cyl D (coh Q B γ) ∶_) (trans e1 (trans e2 (trans e3 e4)))
          (tm[] (ok pQ wQ wB side lY (mask-up sγ wQ) anyY gQ) (liftS-wf sγ wQ gγ))
        where
        B = arr A' s u
        Y = mask D γ
        c = cohId Q B
        lγ : lenₛ γ ≡ len Q
        lγ = snd (Sb.sub-sc closed sγ)
        scγ : ScSub (len Γ) γ
        scγ = fst (Sb.sub-sc closed sγ)
        lY : lenSel Y ≡ len Q
        lY = trans (lenSel-mask D γ) lγ
        anyY : T (anySel Y)
        anyY = subst T (sym (any-mask D γ)) p
        scB : ScTy (len Q) B
        scB = Sb.ty-sc closed wB
        scc : ScTm (len Q) c
        scc = fst (Sb.sub-sc closed (id-wf wQ))
        lmm : lenₛ (genMm Y) ≡ len Q
        lmm = trans (len-genMm Y) lY
        lmY : lenₛ (genMp Y) ≡ lenₛ (genMm Y)
        lmY = trans (len-genMp Y) (sym (len-genMm Y))
        toγ : ∀ i → T (i <ℕ len Q) → T (i <ℕ lenₛ γ)
        toγ i q = subst (λ m → T (i <ℕ m)) (sym lγ) q
        e1 : cylTy (gen Y) c B [ liftS D γ ]ty ≡ cylTy (gen Y [ liftS D γ ]D) c B
        e1 = cylTy-sub (gen Y) (liftS D γ) lmY c B
               (subst (λ m → ScTm m c) (sym lmm) scc) (subst (λ m → ScTy m B) (sym lmm) scB)
        e2 : cylTy (gen Y [ liftS D γ ]D) c B ≡ cylTy (pre γ D) c B
        e2 = Ext.cylTy-ext (gen Y [ liftS D γ ]D) (pre γ D) (len Q) (gm D γ) (gp D γ (sameU γ scγ))
               (λ i q → sel-mask D γ i (toγ i q)) (λ i q r → gth D γ i (toγ i q) r) c B scB
        e3 : cylTy (pre γ D) c B ≡ cylTy D (c [ γ ]tm) (B [ γ ]ty)
        e3 = sym (cylTy-pre D γ c B (subst (λ m → ScTm m c) (sym lγ) scc) (subst (λ m → ScTy m B) (sym lγ) scB))
        e4 : cylTy D (c [ γ ]tm) (B [ γ ]ty) ≡ cylTy D (coh Q B γ) (B [ γ ]ty)
        e4 = cong (λ X → cylTy D (coh Q B X) (B [ γ ]ty))
               (subst (λ m → idS m ∘ γ ≡ γ) lγ (idS∘ γ γ (λ i _ → refl)))
      cyl-wf (cst-wf {()} _ _) g p

      liftS-wf : ∀ {γ Q} → Γ ⊢sub γ ∶ Q → Q ⊢ctx → AllGoodS Good γ → Δ ⊢sub liftS D γ ∶ cylCtx Q (mask D γ)
      liftS-wf (⟨⟩-wf w) wQ g = ⟨⟩-wf wΔ
      liftS-wf (,-wf {σ = γ} {Δ = Q} {t} {A} sγ dt) (▸-wf wQ wA) (gγ , gt) =
        go (touched D t) refl
        where
        Y = mask D γ
        a = t [ mm D ]tm
        b = t [ mp D ]tm
        q = len Q
        Lw = liftS-wf sγ wQ gγ
        lγ : lenₛ γ ≡ len Q
        lγ = snd (Sb.sub-sc closed sγ)
        scγ : ScSub (len Γ) γ
        scγ = fst (Sb.sub-sc closed sγ)
        lY : lenSel Y ≡ len Q
        lY = trans (lenSel-mask D γ) lγ
        scA : ScTy (len Q) A
        scA = Sb.ty-sc closed wA
        scAγ : ScTy (lenₛ γ) A
        scAγ = subst (λ m → ScTy m A) (sym lγ) scA
        scAm : ScTy (lenₛ (genMm Y)) A
        scAm = subst (λ m → ScTy m A) (sym (trans (len-genMm Y) lY)) scA
        scAp : ScTy (lenₛ (genMp Y)) A
        scAp = subst (λ m → ScTy m A) (sym (trans (len-genMp Y) lY)) scA
        lL : lenₛ (liftS D γ) ≡ cnt Y
        lL = len-liftS D γ
        scMp : ScSub (lenₛ (liftS D γ)) (genMp Y)
        scMp = subst (λ m → ScSub m (genMp Y)) (sym lL) (sc-genMp Y)
        scMm : ScSub (lenₛ (liftS D γ)) (genMm Y)
        scMm = subst (λ m → ScSub m (genMm Y)) (sym lL) (sc-genMm Y)

        dm : Δ ⊢tm a ∶ A [ genMm Y ]ty [ liftS D γ ]ty
        dm = subst (Δ ⊢tm a ∶_)
               (trans (Sb.assoc-ty A γ (mm D) scAγ)
               (trans (cong (A [_]ty) (sym (gm D γ))) (sym (Sb.assoc-ty A (genMm Y) (liftS D γ) scAm))))
               (tm[] dt vmm)

        dp : Δ ⊢tm b ∶ A [ genMp Y ]ty [ liftS D γ ,ₛ a ]ty
        dp = subst (Δ ⊢tm b ∶_)
               (trans (Sb.assoc-ty A γ (mp D) scAγ)
               (trans (cong (A [_]ty) (sym (gp D γ (sameU γ scγ))))
               (trans (sym (Sb.assoc-ty A (genMp Y) (liftS D γ) scAp))
                      (sym (Sb.ext-ty (A [ genMp Y ]ty) (liftS D γ) a (Sb.sc-ty[] A (genMp Y) scAp scMp))))))
               (tm[] dt vmp)

        ρ₂ = liftS D γ ,ₛ a ,ₛ b
        G  = gen (Y ◂ true)

        ext2-tm : ∀ x → ScTm (lenₛ (liftS D γ)) x → x [ ρ₂ ]tm ≡ x [ liftS D γ ]tm
        ext2-tm x sx = trans (Sb.ext-tm x (liftS D γ ,ₛ a) b (Sb.scTm-suc x sx)) (Sb.ext-tm x (liftS D γ) a sx)

        ext2-sub : ∀ τ → ScSub (lenₛ (liftS D γ)) τ → τ ∘ ρ₂ ≡ τ ∘ liftS D γ
        ext2-sub τ sτ = trans (Sb.ext-sub τ (liftS D γ ,ₛ a) b (Sb.scSub-suc τ sτ)) (Sb.ext-sub τ (liftS D γ) a sτ)

        lk-a : lookupₛ ρ₂ (cnt Y) ≡ a
        lk-a = trans (cong (lookupₛ ρ₂) (sym lL))
                 (trans (lk-ext (liftS D γ ,ₛ a) b (lenₛ (liftS D γ)) (n<sn (lenₛ (liftS D γ)))) (lk-top (liftS D γ) a))

        lk-b : lookupₛ ρ₂ (suc (cnt Y)) ≡ b
        lk-b = trans (cong (λ m → lookupₛ ρ₂ (suc m)) (sym lL)) (lk-top (liftS D γ ,ₛ a) b)

        emm : genMm (Y ◂ true) ∘ ρ₂ ≡ (γ ,ₛ t) ∘ mm D
        emm = cong₂ _,ₛ_ (trans (ext2-sub (genMm Y) scMm) (gm D γ)) lk-a

        emp : genMp (Y ◂ true) ∘ ρ₂ ≡ (γ ,ₛ t) ∘ mp D
        emp = cong₂ _,ₛ_ (trans (ext2-sub (genMp Y) scMp) (gp D γ (sameU γ scγ))) lk-b

        toγ : ∀ i → T (i <ℕ len Q) → T (i <ℕ lenₛ γ)
        toγ i r = subst (λ m → T (i <ℕ m)) (sym lγ) r

        toY : ∀ i → T (i <ℕ len Q) → T (i <ℕ lenSel Y)
        toY i r = subst (λ m → T (i <ℕ m)) (sym lY) r

        lowSel : ∀ i → T (i <ℕ len Q) → selAt (Y ◂ true) i ≡ selAt Y i
        lowSel i r = if-f (<→≢' i (lenSel Y) (toY i r))

        esel : ∀ i → T (i <ℕ len Q) → selAt (Y ◂ true) i ≡ touched D (lookupₛ (γ ,ₛ t) i)
        esel i r = trans (lowSel i r) (trans (sel-mask D γ i (toγ i r)) (cong (touched D) (sym (lk-ext γ t i (toγ i r)))))

        eth : ∀ i → T (i <ℕ len Q) → T (selAt (Y ◂ true) i) →
              lookupₛ (genTh (Y ◂ true)) i [ ρ₂ ]tm ≡ cyl D (lookupₛ (γ ,ₛ t) i)
        eth i r u' =
          trans (cong (_[ ρ₂ ]tm) (lk-ext (genTh Y) _ i (subst (λ m → T (i <ℕ m)) (sym (len-genTh Y)) (toY i r))))
          (trans (ext2-tm (lookupₛ (genTh Y) i) (subst (λ m → ScTm m (lookupₛ (genTh Y) i)) (sym lL) (sc-genTh Y i (toY i r) u'')))
          (trans (gth D γ i (toγ i r) u'') (cong (cyl D) (sym (lk-ext γ t i (toγ i r))))))
          where u'' : T (selAt Y i)
                u'' = subst T (lowSel i r) u'

        lG : lenₛ (genMm (Y ◂ true)) ≡ suc (len Q)
        lG = cong suc (trans (len-genMm Y) lY)

        lγt : lenₛ (γ ,ₛ t) ≡ suc (len Q)
        lγt = cong suc lγ

        eqc : cylTy G (var q) A [ ρ₂ ]ty ≡ cylTy D t (A [ γ ]ty)
        eqc =
          trans (cylTy-sub G ρ₂ (trans (len-genMp (Y ◂ true)) (sym (len-genMm (Y ◂ true)))) (var q) A
                   (subst (λ m → T (q <ℕ m)) (sym lG) (n<sn q))
                   (subst (λ m → ScTy m A) (sym lG) (sc-mono-ty A (le-add (len Q) 1) scA)))
          (trans (Ext.cylTy-ext (G [ ρ₂ ]D) (pre (γ ,ₛ t) D) (len Q) emm emp esel eth (var q) A scA)
          (trans (sym (cylTy-pre D (γ ,ₛ t) (var q) A
                         (subst (λ m → T (q <ℕ m)) (sym lγt) (n<sn q))
                         (subst (λ m → ScTy m A) (sym lγt) (sc-mono-ty A (le-add (len Q) 1) scA))))
                 (cong₂ (cylTy D) (trans (cong (lookupₛ (γ ,ₛ t)) (sym lγ)) (lk-top γ t))
                                  (Sb.ext-ty A γ t scAγ))))

        go : ∀ v → touched D t ≡ v →
             Δ ⊢sub liftOne (liftS D γ) a b (cyl D t) v ∶ cylCtx (Q ▸ A) (mask D γ ◂ v)
        go false e = ,-wf Lw dm
        go true  e = ,-wf (,-wf (,-wf Lw dm) dp)
                          (subst (Δ ⊢tm cyl D t ∶_) (sym eqc) (cyl-wf dt gt (subst T (sym e) tt)))
