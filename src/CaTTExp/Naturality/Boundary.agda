------------------------------------------------------------------------
-- The boundary cells a_t, b_t of a naturality cylinder are well typed
-- (ledger C1d), in every dimension.
--
-- For a datum D on Γ into Δ whose two copies are typed and whose
-- selection is up-closed (`BaseD`; no cylinders of variables are
-- assumed), and a term Γ ⊢ t ∶ A:
--
--   P-wf  : Δ ⊢tm P D k t A ∶ TP D k A      (k ≤ dim A)
--   L-wf  : Δ ⊢tm L D k t A ∶ TL D k A      (k ≤ dim A)
--   cylTy-wf : Δ ⊢ty cylTy D t A = (a_t → b_t)
--
-- given cylinders of the touched iterated boundaries of A (`CylBd A`):
-- the whiskers of a_t, b_t are by those boundary cylinders. When A's
-- boundaries are variables, `CylBd A` is read off the cylinders of
-- the variables; in general it is supplied by cyl-wf
-- (CaTTExp.Naturality.Typing).
--
-- The proof follows the recursion of P and L: the k-th whisker is
-- typed by rwT-wf / lwT-wf, and the type it lands in is TP (k+1) A
-- (rw-ty, lw-ty) because the k-type and k-target of TP k A are
-- TP k and P k of the k-th base and target of A (tyK-TP, tgtK-TP, and
-- dually tyK-TL, srcK-TL). An omitted whisker (untouched boundary)
-- changes nothing (rw-omit, lw-omit), because an untouched term with
-- an untouched type has trivial whiskered copies (triv-P, triv-L).
------------------------------------------------------------------------
module CaTTExp.Naturality.Boundary where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn; <→≢)
open import CaTTExp.Derived using (tm-ty; T-≡; nB; wK; lK; subst₂)
open import CaTTExp.DerivedBoundary
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Commute
  using (lt-ne; eq-sound; nB-sub; if-t; if-f; dim-baseAt; anyL-++; anyL-ty; anyL-ext-ty; img)
open import CaTTExp.Naturality.Typing
  using (∨-false-l; ∨-false-r; T-∨-false; anyL-false; lk-untouched)

------------------------------------------------------------------------
-- Arithmetic and syntax.

private
  arr-inj₂ : ∀ {A B s t u v} → arr A s t ≡ arr B u v → s ≡ u
  arr-inj₂ refl = refl

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

==-refl : ∀ n → (n ==ℕ n) ≡ true
==-refl n = T-≡ (==ℕ-refl n)

n∸n : ∀ n → n ∸ n ≡ 0
n∸n zero    = refl
n∸n (suc n) = n∸n n

∸-suc : ∀ k n → T (k <ℕ n) → n ∸ k ≡ suc (n ∸ suc k)
∸-suc zero    (suc n) _ = refl
∸-suc (suc k) (suc n) p = ∸-suc k n p

-- k ≤ n: either k = n or k < n.
data Cmp (k n : Nat) : Set where
  top : k ≡ n → Cmp k n
  low : T (k <ℕ n) → Cmp k n

cmp : ∀ k n → T (k <ℕ suc n) → Cmp k n
cmp k n p with k ==ℕ n in e
... | true  = top (eq-sound e)
... | false = low (lt-ne k n p e)

baseAt-top : ∀ A → baseAt (dim A) A ≡ A
baseAt-top ⋆           = refl
baseAt-top (arr A s u) = if-t (==-refl (dim A))

baseAt-low : ∀ k A s u → T (k <ℕ suc (dim A)) → baseAt k (arr A s u) ≡ baseAt k A
baseAt-low k A s u p = if-f (<→≢ k (suc (dim A)) p)

tgtAt-top : ∀ A s u → tgtAt (dim A) (arr A s u) ≡ u
tgtAt-top A s u = if-t (==-refl (dim A))

tgtAt-low : ∀ k A s u → T (k <ℕ dim A) → tgtAt k (arr A s u) ≡ tgtAt k A
tgtAt-low k A s u p = if-f (<→≢ k (dim A) p)

srcAt-top : ∀ A s u → srcAt (dim A) (arr A s u) ≡ s
srcAt-top A s u = if-t (==-refl (dim A))

srcAt-low : ∀ k A s u → T (k <ℕ dim A) → srcAt k (arr A s u) ≡ srcAt k A
srcAt-low k A s u p = if-f (<→≢ k (dim A) p)

-- The top-dimensional type, source and target of a cell type.
tyK-top : ∀ k C s t → dim C ≡ k → tyK k (arr C s t) ≡ C
tyK-top .(dim C) C s t refl = sym (arr-inj₁ (C-sph (dim C) (arr C s t) refl))

srcK-top : ∀ k C s t → dim C ≡ k → srcK k (arr C s t) ≡ s
srcK-top .(dim C) C s t refl = sym (arr-inj₂ (C-sph (dim C) (arr C s t) refl))

tgtK-top : ∀ k C s t → dim C ≡ k → tgtK k (arr C s t) ≡ t
tgtK-top .(dim C) C s t refl = sym (arr-inj₃ (C-sph (dim C) (arr C s t) refl))

-- Untouched types have untouched targets and sources.
fv-tgtAt : ∀ f k A → anyL f (fvTy A) ≡ false → T (k <ℕ dim A) → anyL f (fvTm (tgtAt k A)) ≡ false
fv-tgtAt f k (arr A s u) e p with cmp k (dim A) p
... | top refl = subst (λ w → anyL f (fvTm w) ≡ false) (sym (tgtAt-top A s u))
                   (∨-false-r (trans (sym (anyL-++ f (fvTm s) (fvTm u))) (∨-false-r e1)))
  where e1 = trans (sym (anyL-++ f (fvTy A) (fvTm s ++ fvTm u))) e
... | low q    = subst (λ w → anyL f (fvTm w) ≡ false) (sym (tgtAt-low k A s u q))
                   (fv-tgtAt f k A (∨-false-l e1) q)
  where e1 = trans (sym (anyL-++ f (fvTy A) (fvTm s ++ fvTm u))) e

fv-srcAt : ∀ f k A → anyL f (fvTy A) ≡ false → T (k <ℕ dim A) → anyL f (fvTm (srcAt k A)) ≡ false
fv-srcAt f k (arr A s u) e p with cmp k (dim A) p
... | top refl = subst (λ w → anyL f (fvTm w) ≡ false) (sym (srcAt-top A s u))
                   (∨-false-l (trans (sym (anyL-++ f (fvTm s) (fvTm u))) (∨-false-r e1)))
  where e1 = trans (sym (anyL-++ f (fvTy A) (fvTm s ++ fvTm u))) e
... | low q    = subst (λ w → anyL f (fvTm w) ≡ false) (sym (srcAt-low k A s u q))
                   (fv-srcAt f k A (∨-false-l e1) q)
  where e1 = trans (sym (anyL-++ f (fvTy A) (fvTm s ++ fvTm u))) e

------------------------------------------------------------------------
-- The shape of the whiskered types TP, TL.

module Shape (K : Filler) (D : Datum) where
  open Cyl K

  dim-TP : ∀ k A → T (k <ℕ suc (dim A)) → dim (TP D k A) ≡ dim A
  dim-TP zero    A           p = dim[] A (mm D)
  dim-TP (suc k) ⋆           ()
  dim-TP (suc k) (arr A s u) p with k ==ℕ dim A in e
  ... | true  = cong suc (dim-TP k A p)
  ... | false = cong suc (dim-TP (suc k) A (lt-ne k (dim A) p e))

  dim-TL : ∀ k A → T (k <ℕ suc (dim A)) → dim (TL D k A) ≡ dim A
  dim-TL zero    A           p = dim[] A (mp D)
  dim-TL (suc k) ⋆           ()
  dim-TL (suc k) (arr A s u) p with k ==ℕ dim A in e
  ... | true  = cong suc (dim-TP k A p)
  ... | false = cong suc (dim-TL (suc k) A (lt-ne k (dim A) p e))

  -- Below the top, TP and TL act on the three parts of a type.
  TP-low : ∀ k A s u → T (k <ℕ suc (dim A)) → TP D k (arr A s u) ≡ arr (TP D k A) (P D k s A) (P D k u A)
  TP-low zero    A s u p = refl
  TP-low (suc k) A s u p = if-f (<→≢ k (dim A) p)

  TL-low : ∀ k A s u → T (k <ℕ suc (dim A)) → TL D k (arr A s u) ≡ arr (TL D k A) (L D k s A) (L D k u A)
  TL-low zero    A s u p = refl
  TL-low (suc k) A s u p = if-f (<→≢ k (dim A) p)

  -- At the top, both are the type of a_t and b_t.
  TP-top : ∀ A s u → TP D (suc (dim A)) (arr A s u) ≡ arr (TP D (dim A) A) (P D (dim A) s A) (L D (dim A) u A)
  TP-top A s u = if-t (==-refl (dim A))

  TL-top : ∀ A s u → TL D (suc (dim A)) (arr A s u) ≡ arr (TP D (dim A) A) (P D (dim A) s A) (L D (dim A) u A)
  TL-top A s u = if-t (==-refl (dim A))

  TL≡TP : ∀ A → TL D (dim A) A ≡ TP D (dim A) A
  TL≡TP ⋆           = refl
  TL≡TP (arr A s u) = trans (TL-top A s u) (sym (TP-top A s u))

  -- The k-type and k-target of TP k A, the k-type and k-source of TL k A.
  tyK-TP : ∀ k A → T (k <ℕ dim A) → tyK k (TP D k A) ≡ TP D k (baseAt k A)
  tyK-TP k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (tyK k) (TP-low k A s u p))
    (trans (tyK-top k (TP D k A) _ _ (dim-TP k A p))
           (cong (TP D k) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (tyK k) (TP-low k A s u p))
    (trans (tyK-arr k (TP D k A) _ _ (subst (λ m → T (k <ℕ m)) (sym (dim-TP k A p)) q))
    (trans (tyK-TP k A q) (cong (TP D k) (sym (baseAt-low k A s u p)))))

  tgtK-TP : ∀ k A → T (k <ℕ dim A) → tgtK k (TP D k A) ≡ P D k (tgtAt k A) (baseAt k A)
  tgtK-TP k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (tgtK k) (TP-low k A s u p))
    (trans (tgtK-top k (TP D k A) _ _ (dim-TP k A p))
           (cong₂ (P D k) (sym (tgtAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (tgtK k) (TP-low k A s u p))
    (trans (tgtK-arr k (TP D k A) _ _ (subst (λ m → T (k <ℕ m)) (sym (dim-TP k A p)) q))
    (trans (tgtK-TP k A q) (cong₂ (P D k) (sym (tgtAt-low k A s u q)) (sym (baseAt-low k A s u p)))))

  tyK-TL : ∀ k A → T (k <ℕ dim A) → tyK k (TL D k A) ≡ TP D k (baseAt k A)
  tyK-TL k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (tyK k) (TL-low k A s u p))
    (trans (tyK-top k (TL D k A) _ _ (dim-TL k A p))
    (trans (TL≡TP A) (cong (TP D k) (sym (trans (baseAt-low k A s u p) (baseAt-top A))))))
  ... | low q =
    trans (cong (tyK k) (TL-low k A s u p))
    (trans (tyK-arr k (TL D k A) _ _ (subst (λ m → T (k <ℕ m)) (sym (dim-TL k A p)) q))
    (trans (tyK-TL k A q) (cong (TP D k) (sym (baseAt-low k A s u p)))))

  srcK-TL : ∀ k A → T (k <ℕ dim A) → srcK k (TL D k A) ≡ L D k (srcAt k A) (baseAt k A)
  srcK-TL k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (srcK k) (TL-low k A s u p))
    (trans (srcK-top k (TL D k A) _ _ (dim-TL k A p))
           (cong₂ (L D k) (sym (srcAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (srcK k) (TL-low k A s u p))
    (trans (srcK-arr k (TL D k A) _ _ (subst (λ m → T (k <ℕ m)) (sym (dim-TL k A p)) q))
    (trans (srcK-TL k A q) (cong₂ (L D k) (sym (srcAt-low k A s u q)) (sym (baseAt-low k A s u p)))))

  ----------------------------------------------------------------------
  -- The k-th whisker lands in TP (k+1) A, resp. TL (k+1) A.

  rw-ty : ∀ k A (p : T (k <ℕ dim A)) → touched D (tgtAt k A) ≡ true → ∀ c →
          wK k (dim A ∸ suc k) [ σR c (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A)) ]ty
            ≡ TP D (suc k) A
  rw-ty k (arr A s u) p e c with cmp k (dim A) p
  ... | top refl =
    trans (cong (λ j → wK k j [ σR c C z h ]ty) (n∸n k))
    (trans (rwT-ty0 k c C z h (dim-TP k (arr A s u) (<-suc k _ p)))
    (trans (cong₃ arr (trans (cong (tyK k) (TP-low k A s u p)) (tyK-top k (TP D k A) _ _ (dim-TP k A p)))
                      (trans (cong (srcK k) (TP-low k A s u p)) (srcK-top k (TP D k A) _ _ (dim-TP k A p)))
                      (cong₂ (L D k) (tgtAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A))))
           (sym (TP-top A s u))))
    where
    C = TP D k (arr A s u)
    z = L D k (tgtAt k (arr A s u)) (baseAt k (arr A s u))
    h = cyl D (tgtAt k (arr A s u))
  ... | low q =
    trans (cong₂ (λ w B → wK k (dim A ∸ k) [ σR c (TP D k (arr A s u)) (L D k w B) (cyl D w) ]ty)
                 (tgtAt-low k A s u q) (baseAt-low k A s u p))
    (trans (cong (λ j → wK k j [ σR c (TP D k (arr A s u)) z h ]ty) (∸-suc k (dim A) q))
    (trans (cong (λ C → wK k (suc j) [ σR c C z h ]ty) (TP-low k A s u p))
    (trans (rwT-ty k j c (TP D k A) (P D k s A) (P D k u A) z h (trans (dim-TP k A p) (nB-sub k (dim A) q)))
    (trans (cong₃ arr (rw-ty k A q e' (P D k s A))
                      (cong (rwI k (dim A) (P D k s A) (TP D k A) z h) (sym e'))
                      (cong (rwI k (dim A) (P D k u A) (TP D k A) z h) (sym e')))
           (sym (TP-low (suc k) A s u q))))))
    where
    j = dim A ∸ suc k
    z = L D k (tgtAt k A) (baseAt k A)
    h = cyl D (tgtAt k A)
    e' : touched D (tgtAt k A) ≡ true
    e' = trans (cong (touched D) (sym (tgtAt-low k A s u q))) e

  lw-ty : ∀ k A (p : T (k <ℕ dim A)) → touched D (srcAt k A) ≡ true → ∀ c →
          lK k (dim A ∸ suc k) [ σL k (dim A ∸ suc k) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) c (TL D k A) ]ty
            ≡ TL D (suc k) A
  lw-ty k (arr A s u) p e c with cmp k (dim A) p
  ... | top refl =
    trans (cong (λ j → lK k j [ σL k j h x c C ]ty) (n∸n k))
    (trans (lwT-ty0 k h x c C (dim-TL k (arr A s u) (<-suc k _ p)))
    (trans (cong₃ arr (trans (cong (tyK k) (TL-low k A s u p))
                        (trans (tyK-top k (TL D k A) _ _ (dim-TL k A p)) (TL≡TP A)))
                      (cong₂ (P D k) (srcAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A)))
                      (trans (cong (tgtK k) (TL-low k A s u p)) (tgtK-top k (TL D k A) _ _ (dim-TL k A p))))
           (sym (TL-top A s u))))
    where
    C = TL D k (arr A s u)
    x = P D k (srcAt k (arr A s u)) (baseAt k (arr A s u))
    h = cyl D (srcAt k (arr A s u))
  ... | low q =
    trans (cong₂ (λ w B → lK k (dim A ∸ k) [ σL k (dim A ∸ k) (cyl D w) (P D k w B) c (TL D k (arr A s u)) ]ty)
                 (srcAt-low k A s u q) (baseAt-low k A s u p))
    (trans (cong (λ m → lK k m [ σL k m h x c (TL D k (arr A s u)) ]ty) (∸-suc k (dim A) q))
    (trans (cong (λ C → lK k (suc j) [ σL k (suc j) h x c C ]ty) (TL-low k A s u p))
    (trans (lwT-ty k j h x c (TL D k A) (L D k s A) (L D k u A) (trans (dim-TL k A p) (nB-sub k (dim A) q)))
    (trans (cong₃ arr (lw-ty k A q e' (L D k s A))
                      (cong (lwI k (dim A) h x (L D k s A) (TL D k A)) (sym e'))
                      (cong (lwI k (dim A) h x (L D k u A) (TL D k A)) (sym e')))
           (sym (TL-low (suc k) A s u q))))))
    where
    j = dim A ∸ suc k
    x = P D k (srcAt k A) (baseAt k A)
    h = cyl D (srcAt k A)
    e' : touched D (srcAt k A) ≡ true
    e' = trans (cong (touched D) (sym (srcAt-low k A s u q))) e

  -- An omitted whisker: the boundary w is untouched and its two
  -- whiskered copies agree.
  rw-omit : ∀ k A (p : T (k <ℕ dim A)) → touched D (tgtAt k A) ≡ false →
            P D k (tgtAt k A) (baseAt k A) ≡ L D k (tgtAt k A) (baseAt k A) →
            TP D k A ≡ TP D (suc k) A
  rw-omit k (arr A s u) p e H with cmp k (dim A) p
  ... | top refl =
    trans (TP-low k A s u p)
    (trans (cong (arr (TP D k A) (P D k s A))
             (trans (cong₂ (P D k) (sym (tgtAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A))))
             (trans H (cong₂ (L D k) (tgtAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A))))))
           (sym (TP-top A s u)))
  ... | low q =
    trans (TP-low k A s u p)
    (trans (cong₃ arr (rw-omit k A q e' H')
                      (cong (rwI k (dim A) (P D k s A) (TP D k A) z h) (sym e'))
                      (cong (rwI k (dim A) (P D k u A) (TP D k A) z h) (sym e')))
           (sym (TP-low (suc k) A s u q)))
    where
    z = L D k (tgtAt k A) (baseAt k A)
    h = cyl D (tgtAt k A)
    e' : touched D (tgtAt k A) ≡ false
    e' = trans (cong (touched D) (sym (tgtAt-low k A s u q))) e
    H' : P D k (tgtAt k A) (baseAt k A) ≡ L D k (tgtAt k A) (baseAt k A)
    H' = subst₂ (λ w B → P D k w B ≡ L D k w B) (tgtAt-low k A s u q) (baseAt-low k A s u p) H

  lw-omit : ∀ k A (p : T (k <ℕ dim A)) → touched D (srcAt k A) ≡ false →
            L D k (srcAt k A) (baseAt k A) ≡ P D k (srcAt k A) (baseAt k A) →
            TL D k A ≡ TL D (suc k) A
  lw-omit k (arr A s u) p e H with cmp k (dim A) p
  ... | top refl =
    trans (TL-low k A s u p)
    (trans (cong₃ arr (TL≡TP A)
                      (trans (cong₂ (L D k) (sym (srcAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A))))
                      (trans H (cong₂ (P D k) (srcAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A)))))
                      refl)
           (sym (TL-top A s u)))
  ... | low q =
    trans (TL-low k A s u p)
    (trans (cong₃ arr (lw-omit k A q e' H')
                      (cong (lwI k (dim A) h x (L D k s A) (TL D k A)) (sym e'))
                      (cong (lwI k (dim A) h x (L D k u A) (TL D k A)) (sym e')))
           (sym (TL-low (suc k) A s u q)))
    where
    x = P D k (srcAt k A) (baseAt k A)
    h = cyl D (srcAt k A)
    e' : touched D (srcAt k A) ≡ false
    e' = trans (cong (touched D) (sym (srcAt-low k A s u q))) e
    H' : L D k (srcAt k A) (baseAt k A) ≡ P D k (srcAt k A) (baseAt k A)
    H' = subst₂ (λ w B → L D k w B ≡ P D k w B) (srcAt-low k A s u q) (baseAt-low k A s u p) H

  -- A term over an untouched type: every whisker is omitted.
  triv-P : ∀ u B → anyL (sel D) (fvTy B) ≡ false → ∀ k → T (k <ℕ suc (dim B)) → P D k u B ≡ u [ mm D ]tm
  triv-P u B eB zero    p = refl
  triv-P u B eB (suc k) p =
    trans (cong (rwI k (dim B) (P D k u B) (TP D k B) (L D k (tgtAt k B) (baseAt k B)) (cyl D (tgtAt k B)))
                (fv-tgtAt (sel D) k B eB p))
          (triv-P u B eB k (<-suc k (dim B) p))

  triv-L : ∀ u B → anyL (sel D) (fvTy B) ≡ false → ∀ k → T (k <ℕ suc (dim B)) → L D k u B ≡ u [ mp D ]tm
  triv-L u B eB zero    p = refl
  triv-L u B eB (suc k) p =
    trans (cong (lwI k (dim B) (cyl D (srcAt k B)) (P D k (srcAt k B) (baseAt k B)) (L D k u B) (TL D k B))
                (fv-srcAt (sel D) k B eB p))
          (triv-L u B eB k (<-suc k (dim B) p))

------------------------------------------------------------------------
-- Typing.

-- A datum without cylinders of variables: typed copies, equal copies
-- of unselected variables, up-closed selection.
record BaseD (D : Datum) (Γ Δ : Ctx) : Set where
  field
    bmm   : Δ ⊢sub mm D ∶ Γ
    bmp   : Δ ⊢sub mp D ∶ Γ
    bsame : ∀ x → T (x <ℕ len Γ) → sel D x ≡ false → lookupₛ (mm D) x ≡ lookupₛ (mp D) x
    bup   : ∀ x A → lookup Γ x ≡ just A → sel D x ≡ false → anyL (sel D) (fvTy A) ≡ false

tgtAt-wf : ∀ {Γ} k A → Γ ⊢ty A → T (k <ℕ dim A) → Γ ⊢tm tgtAt k A ∶ baseAt k A
tgtAt-wf {Γ} k (arr A s u) (arr-wf ds du) p with cmp k (dim A) p
... | top refl = subst₂ (Γ ⊢tm_∶_) (sym (tgtAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A))) du
... | low q    = subst₂ (Γ ⊢tm_∶_) (sym (tgtAt-low k A s u q)) (sym (baseAt-low k A s u p)) (tgtAt-wf k A (tm-ty ds) q)

srcAt-wf : ∀ {Γ} k A → Γ ⊢ty A → T (k <ℕ dim A) → Γ ⊢tm srcAt k A ∶ baseAt k A
srcAt-wf {Γ} k (arr A s u) (arr-wf ds du) p with cmp k (dim A) p
... | top refl = subst₂ (Γ ⊢tm_∶_) (sym (srcAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A))) ds
... | low q    = subst₂ (Γ ⊢tm_∶_) (sym (srcAt-low k A s u q)) (sym (baseAt-low k A s u p)) (srcAt-wf k A (tm-ty ds) q)

module Typed (K : Filler) where
  open Cyl K

  -- Cylinders of the touched iterated boundaries of a type.
  module _ (D : Datum) (Δ : Ctx) where
    CylT : Tm → Ty → Set
    CylT t A = T (touched D t) → Δ ⊢tm cyl D t ∶ cylTy D t A

    CylBd : Ty → Set
    CylBd ⋆           = ⊤
    CylBd (arr A s u) = CylBd A × CylT s A × CylT u A

  module _ {D : Datum} {Δ : Ctx} where
    bd-tgt : ∀ k A → CylBd D Δ A → T (k <ℕ dim A) → CylT D Δ (tgtAt k A) (baseAt k A)
    bd-tgt k (arr A s u) b p with cmp k (dim A) p
    ... | top refl = subst₂ (CylT D Δ) (sym (tgtAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))
                       (snd (snd b))
    ... | low q    = subst₂ (CylT D Δ) (sym (tgtAt-low k A s u q)) (sym (baseAt-low k A s u p))
                       (bd-tgt k A (fst b) q)

    bd-src : ∀ k A → CylBd D Δ A → T (k <ℕ dim A) → CylT D Δ (srcAt k A) (baseAt k A)
    bd-src k (arr A s u) b p with cmp k (dim A) p
    ... | top refl = subst₂ (CylT D Δ) (sym (srcAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))
                       (fst (snd b))
    ... | low q    = subst₂ (CylT D Δ) (sym (srcAt-low k A s u q)) (sym (baseAt-low k A s u p))
                       (bd-src k A (fst b) q)

  module _ {D : Datum} {Γ Δ : Ctx} (V : BaseD D Γ Δ) where
    open BaseD V
    open Shape K D

    mutual
      same-tm : ∀ t → ScTm (len Γ) t → touched D t ≡ false → t [ mm D ]tm ≡ t [ mp D ]tm
      same-tm (var x)     p e = bsame x p (∨-false-l e)
      same-tm (coh Q B γ) p e = cong (coh Q B) (same-sub γ p e)
      same-tm (cst ())    p e

      same-sub : ∀ γ → ScSub (len Γ) γ → anyL (sel D) (fvSub γ) ≡ false → γ ∘ mm D ≡ γ ∘ mp D
      same-sub ⟨⟩       p       e = refl
      same-sub (γ ,ₛ t) (p , q) e =
        cong₂ _,ₛ_ (same-sub γ p (∨-false-l e')) (same-tm t q (∨-false-r e'))
        where e' = trans (sym (anyL-++ (sel D) (fvSub γ) (fvTm t))) e

    same-ty : ∀ A → ScTy (len Γ) A → anyL (sel D) (fvTy A) ≡ false → A [ mm D ]ty ≡ A [ mp D ]ty
    same-ty ⋆           _           _ = refl
    same-ty (arr A s u) (a , p , q) e =
      cong₃ arr (same-ty A a (∨-false-l e1)) (same-tm s p (∨-false-l e2)) (same-tm u q (∨-false-r e2))
      where
      e1 = trans (sym (anyL-++ (sel D) (fvTy A) (fvTm s ++ fvTm u))) e
      e2 = trans (sym (anyL-++ (sel D) (fvTm s) (fvTm u))) (∨-false-r e1)

    -- An untouched term has an untouched type.
    UT : ∀ {t A} → Γ ⊢tm t ∶ A → touched D t ≡ false → anyL (sel D) (fvTy A) ≡ false
    UT (var-wf {i} {A} w eq) e = bup i A eq (∨-false-l e)
    UT (coh-wf {Δ = Q} {A'} {s} {u} {γ} pQ wQ wB side sγ) e =
      trans (anyL-ty (sel D) γ (arr A' s u))
      (trans (anyL-ext-ty (img (sel D) γ) (λ _ → false) (λ i q → lk-untouched (sel D) γ i e q) (arr A' s u) scB)
             (anyL-false (fvTy (arr A' s u))))
      where scB = subst (λ m → ScTy m (arr A' s u)) (sym (snd (Sb.sub-sc closed sγ))) (Sb.ty-sc closed wB)
    UT (cst-wf {()} _ _) e

    -- The two whiskered copies of an untouched boundary agree.
    triv : ∀ {w B} → Γ ⊢tm w ∶ B → touched D w ≡ false → ∀ k → dim B ≡ k →
           P D k w B ≡ L D k w B
    triv {w} {B} dw e k eB =
      trans (triv-P w B uB k le)
      (trans (same-tm w (Sb.tm-sc closed dw) e) (sym (triv-L w B uB k le)))
      where
      uB = UT dw e
      le = subst (λ m → T (k <ℕ suc m)) (sym eB) (n<sn k)

    private
      cylTy-k : ∀ {w B} k → dim B ≡ k → cylTy D w B ≡ arr (TP D k B) (P D k w B) (L D k w B)
      cylTy-k {w} {B} k eB = cong (λ m → arr (TP D m B) (P D m w B) (L D m w B)) eB

    module _ {t A} (dt : Γ ⊢tm t ∶ A) (b : CylBd D Δ A) where
      private
        dA = tm-ty dt

      stepP : ∀ k (p : T (k <ℕ dim A)) v → touched D (tgtAt k A) ≡ v →
              Δ ⊢tm P D k t A ∶ TP D k A →
              Δ ⊢tm rwI k (dim A) (P D k t A) (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A)) v
                ∶ TP D (suc k) A
      stepP k p true e d =
        subst (Δ ⊢tm rwT k (dim A ∸ suc k) (P D k t A) (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A)) ∶_)
          (rw-ty k A p e (P D k t A))
          (rwT-wf k (dim A ∸ suc k) d (trans (dim-TP k A (<-suc k (dim A) p)) (nB-sub k (dim A) p))
            (subst (Δ ⊢tm cyl D w ∶_)
               (trans (cylTy-k k (dim-baseAt k A (<-suc k (dim A) p)))
                      (cong₂ (λ X y → arr X y (L D k w B)) (sym (tyK-TP k A p)) (sym (tgtK-TP k A p))))
               (bd-tgt k A b p (subst T (sym e) tt))))
        where
        w = tgtAt k A
        B = baseAt k A
      stepP k p false e d =
        subst (Δ ⊢tm P D k t A ∶_)
          (rw-omit k A p e (triv (tgtAt-wf k A dA p) e k (dim-baseAt k A (<-suc k (dim A) p)))) d

      stepL : ∀ k (p : T (k <ℕ dim A)) v → touched D (srcAt k A) ≡ v →
              Δ ⊢tm L D k t A ∶ TL D k A →
              Δ ⊢tm lwI k (dim A) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) (L D k t A) (TL D k A) v
                ∶ TL D (suc k) A
      stepL k p true e d =
        subst (Δ ⊢tm lwT k (dim A ∸ suc k) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) (L D k t A) (TL D k A) ∶_)
          (lw-ty k A p e (L D k t A))
          (lwT-wf k (dim A ∸ suc k) d (trans (dim-TL k A (<-suc k (dim A) p)) (nB-sub k (dim A) p))
            (subst (Δ ⊢tm cyl D w ∶_)
               (trans (cylTy-k k (dim-baseAt k A (<-suc k (dim A) p)))
                      (cong₂ (λ X y → arr X (P D k w B) y) (sym (tyK-TL k A p)) (sym (srcK-TL k A p))))
               (bd-src k A b p (subst T (sym e) tt))))
        where
        w = srcAt k A
        B = baseAt k A
      stepL k p false e d =
        subst (Δ ⊢tm L D k t A ∶_)
          (lw-omit k A p e (sym (triv (srcAt-wf k A dA p) e k (dim-baseAt k A (<-suc k (dim A) p))))) d

      P-wf : ∀ k → T (k <ℕ suc (dim A)) → Δ ⊢tm P D k t A ∶ TP D k A
      P-wf zero    p = tm[] dt bmm
      P-wf (suc k) p = stepP k p (touched D (tgtAt k A)) refl (P-wf k (<-suc k (dim A) p))

      L-wf : ∀ k → T (k <ℕ suc (dim A)) → Δ ⊢tm L D k t A ∶ TL D k A
      L-wf zero    p = tm[] dt bmp
      L-wf (suc k) p = stepL k p (touched D (srcAt k A)) refl (L-wf k (<-suc k (dim A) p))

      -- a_t → b_t is a well-formed type of Δ.
      aT-wf : Δ ⊢tm aT D t A ∶ TP D (dim A) A
      aT-wf = P-wf (dim A) (n<sn (dim A))

      bT-wf : Δ ⊢tm bT D t A ∶ TP D (dim A) A
      bT-wf = subst (Δ ⊢tm bT D t A ∶_) (TL≡TP A) (L-wf (dim A) (n<sn (dim A)))

      cylTy-wf : Δ ⊢ty cylTy D t A
      cylTy-wf = arr-wf aT-wf bT-wf
