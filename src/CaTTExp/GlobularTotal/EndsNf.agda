------------------------------------------------------------------------
-- F2c, for the coh case of (1′): the normal forms of the endpoints of
-- a coherence.
--
-- In Θ = ctxOf τ, let u, v : B have normal forms au, av that are
-- diagrams of Θ of dimension dim B labelled by Var(u : B), Var(v : B),
-- with equal boundaries below dim B (they are parallel). If the coh
-- side condition holds, then
--
--   au ≡ bd false (dim B) (idTree τ)   and   av ≡ bd true (dim B) (idTree τ).
--
-- Full case: au = av = idTree τ (Contract.full-nf), and dim Θ ≤ dim B
-- since a top-dimensional variable is a label of au (ExBd.thin-dim),
-- so idTree τ is its own dim B boundary (DimCheck.tree-dim).
-- Op case: au = bd false k (idTree τ), av = bd true k (idTree τ) with
-- k = dim Θ − 1. A label of dimension k survives in au (kid-src), so
-- k ≤ dim B; if k < dim B then au and av agree below dim B, which
-- makes them equal (bd-idem), against DimCheck.bd-distinct.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.EndsNf where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; idTree)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; Ex; dimOf)
open import CaTTExp.GlobularTotal.PsOrd using (ps-ord)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.ExBd using (thin-dim)
open import CaTTExp.GlobularTotal.Labels using (bool-ext)
open import CaTTExp.GlobularTotal.Contract using (full-nf; src-nf; tgt-nf)
open import CaTTExp.GlobularTotal.DimCheck
  using (HasKid; kid-src; bd-idem; bd-distinct; tree-dim; ex-wf; top-label; kid-top)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-T : ∀ a b → T (a ∨ b) → T a ⊎ T b
  ∨-T true  b p = inl tt
  ∨-T false b p = inr p

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  elem-memL : ∀ y xs → elem y xs ≡ memL y xs
  elem-memL y []       = refl
  elem-memL y (x ∷ xs) = cong ((y ==ℕ x) ∨_) (elem-memL y xs)

  ⊆?-sound : ∀ xs ys y → T (⊆? xs ys) → memL y xs ≡ true → memL y ys ≡ true
  ⊆?-sound []       ys y p ()
  ⊆?-sound (x ∷ xs) ys y p m with y ==ℕ x in eq
  ... | true rewrite ==ℕ-sound y x (≡-T eq) = trans (sym (elem-memL x ys)) (T-≡ (∧-fst p))
  ... | false = ⊆?-sound xs ys y (∧-snd {elem x ys} p) m

  ≈?-sound : ∀ xs ys → T (≈? xs ys) → ∀ y → memL y xs ≡ memL y ys
  ≈?-sound xs ys p y =
    bool-ext _ _ (⊆?-sound xs ys y (∧-fst p)) (⊆?-sound ys xs y (∧-snd {⊆? xs ys} p))

  -- a ≤ b as a < suc b
  le-split : ∀ a b → T (a <ℕ suc b) → Σ Nat λ i → b ≡ a + i
  le-split zero    b       p = b , refl
  le-split (suc a) zero    ()
  le-split (suc a) (suc b) p with le-split a b p
  ... | i , e = i , cong suc e

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  ≤-refl : ∀ a → T (a <ℕ suc a)
  ≤-refl zero    = tt
  ≤-refl (suc a) = ≤-refl a

  ≤-weak : ∀ a b → T (a <ℕ suc b) → T (a <ℕ suc (suc b))
  ≤-weak zero    b       p = tt
  ≤-weak (suc a) zero    ()
  ≤-weak (suc a) (suc b) p = ≤-weak a b p

Dim : Nat → LT → Set
Dim d a = ∀ β i → bd β (d + i) a ≡ a

-- u and v agree below dim B (both have the source of B as boundary).
ParB : Ty → LT → LT → Set
ParB ⋆            au av = ⊤
ParB (arr B' _ _) au av = bd false (dim B') au ≡ bd false (dim B') av

module _ (τ : Tree) where

  private
    Θ = ctxOf τ
    Tr = idTree τ
    xT = lab-ex τ

    -- dim Θ ≤ d makes idTree τ its own d-boundary.
    thin-at : ∀ β d → T (dimCtx Θ <ℕ suc d) → bd β d Tr ≡ Tr
    thin-at β d p with le-split (dimCtx Θ) d p
    ... | i , e rewrite e = tree-dim τ β i

  ends-nf : ∀ B u v au av → Ex Θ 0 nothing au → Ex Θ 0 nothing av → Dim (dim B) au → Dim (dim B) av →
            (∀ y → mem y au ≡ memL y (fvTmTy u B)) → (∀ y → mem y av ≡ memL y (fvTmTy v B)) →
            ParB B au av → T (cattSide Θ B u v) →
            (au ≡ bd false (dim B) Tr) × (av ≡ bd true (dim B) Tr) × T (dimCtx Θ <ℕ suc (suc (dim B)))
  ends-nf B u v au av xu xv du dv lu lv pb side with ∨-T (isCoh Θ B u v) (isOp Θ B u v) side
  ... | inl full = eu , ev , ≤-weak (dimCtx Θ) (dim B) dimΘ≤
    where
    au-T : au ≡ Tr
    au-T = full-nf τ au xu (λ y → trans (lu y) (≈?-sound (fvTmTy u B) (varsCtx Θ) (∧-fst full) y))

    av-T : av ≡ Tr
    av-T = full-nf τ av xv (λ y → trans (lv y) (≈?-sound (fvTmTy v B) (varsCtx Θ) (∧-snd {≈? (fvTmTy u B) (varsCtx Θ)} full) y))

    dimΘ≤ : T (dimCtx Θ <ℕ suc (dim B))
    dimΘ≤ with dimCtx Θ in eq
    ... | zero  = tt
    ... | suc k with top-label τ k eq
    ...   | z , m , dz =
      subst (λ n → T (n <ℕ suc (dim B))) dz
        (thin-dim Θ false (dim B) au z xu (trans (cong (λ n → bd false n au) (sym (+0 (dim B)))) (du false 0))
           (trans (cong (mem z) au-T) m))

    eu : au ≡ bd false (dim B) Tr
    eu = trans au-T (sym (thin-at false (dim B) dimΘ≤))

    ev : av ≡ bd true (dim B) Tr
    ev = trans av-T (sym (thin-at true (dim B) dimΘ≤))
  ... | inr op with src-nf τ au xu (λ y → trans (lu y) (≈?-sound (fvTmTy u B) (∂⁻ Θ) (∧-fst op) y))
                  | tgt-nf τ av xv (λ y → trans (lv y) (≈?-sound (fvTmTy v B) (∂⁺ Θ) (∧-snd {≈? (fvTmTy u B) (∂⁻ Θ)} op) y))
  ...   | au-s | av-t with dimCtx Θ in eq
  ...     | zero rewrite au-s | av-t =
    trans (zero-thin false) (sym (thin-at false (dim B) (subst (λ n → T (n <ℕ suc (dim B))) (sym eq) tt))) ,
    trans (zero-thin true) (sym (thin-at true (dim B) (subst (λ n → T (n <ℕ suc (dim B))) (sym eq) tt))) ,
    tt
    where
    zero-thin : ∀ β → bd β 0 Tr ≡ Tr
    zero-thin β = subst (λ n → bd β n Tr ≡ Tr) (trans (+0 (dimCtx Θ)) eq) (tree-dim τ β 0)
  ...     | suc k with kid-src Θ k 0 nothing Tr xT (kid-top τ k eq)
  ...       | y , m , dy with le-split k (dim B)
                (subst (λ n → T (n <ℕ suc (dim B))) dy
                  (thin-dim Θ false (dim B) au y xu
                    (trans (cong (λ n → bd false n au) (sym (+0 (dim B)))) (du false 0))
                    (trans (cong (mem y) au-s) m)))
  ...         | zero , e = trans au-s (cong (λ n → bd false n Tr) (trans (sym (+0 k)) (sym e))) ,
                           trans av-t (cong (λ n → bd true n Tr) (trans (sym (+0 k)) (sym e))) ,
                           subst (λ n → T (k <ℕ suc n)) (trans (sym (+0 k)) (sym e)) (≤-refl k)
  ...         | suc i , e = ⊥-elim (higher B pb e)
    where
    wT = ex-wf Θ 0 nothing Tr xT
    higher : ∀ B → ParB B au av → dim B ≡ k + suc i → ⊥
    higher ⋆ _ e' with trans e' (+-suc k i)
    ... | ()
    higher (arr B' _ _) pb' e' =
      bd-distinct τ k eq
        (trans (sym (bd-idem false false k i Tr wT))
        (trans (cong (λ n → bd false n (bd false k Tr)) (sym d'))
        (trans (cong (bd false (dim B')) (sym au-s))
        (trans pb'
        (trans (cong (bd false (dim B')) av-t)
        (trans (cong (λ n → bd false n (bd true k Tr)) d')
               (bd-idem false true k i Tr wT)))))))
      where
      d' : dim B' ≡ k + i
      d' = suc-inj (trans e' (+-suc k i))
