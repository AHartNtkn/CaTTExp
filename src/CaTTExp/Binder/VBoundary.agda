------------------------------------------------------------------------
-- The boundary cells a_t, b_t of a naturality cylinder are well typed,
-- in binder syntax, with deep types (ledger S26i (2); port of
-- CaTTExp.Naturality.Boundary to Binder.VCyl).
--
-- For a datum D on Γ into Δ with typed copies, equal copies of
-- unselected variables and untouched types of untouched terms
-- (`BaseD`), and a term t with a deep type A in Γ:
--
--   P-wf  : DTm Δ (P D k t A) (TP D k A)      (k ≤ dim A)
--   L-wf  : DTm Δ (L D k t A) (TL D k A)      (k ≤ dim A)
--   cylTy-wf : DTy Δ (cylTy D t A)            (a_t → b_t)
--
-- given cylinders of the touched iterated boundaries of A (`CylBd A`,
-- with deep types). The proof follows Naturality.Boundary: the k-th
-- whisker is typed by VWhisk's rwT-wf / lwT-wf and lands in
-- TP (k+1) A (rw-ty, lw-ty); an omitted whisker changes nothing
-- (rw-omit, lw-omit, triv).
--
-- `but` (an untouched term has an untouched type) is a hypothesis
-- here: in pure CaTT it is proved by induction on typing, which in
-- binder syntax needs the free variables of binder result types. For
-- a suffix selection (every variable from some n on, the form INIT
-- uses) it follows from scoping alone (`but-suffix`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Derived as Dv
open import CaTTExp.GrayCtx.NaturalWF using (n<sn)
open import CaTTExp.Naturality.Raw using (Filler; anyL)
open import CaTTExp.Naturality.Commute using (if-t; if-f; nB-sub)
open import CaTTExp.Naturality.Typing using (∨-false-l; ∨-false-r)
open Dv using (subst₂)

module CaTTExp.Binder.VBoundary
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  (KF : Filler)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark using (MarkRen; ==-self)
open import CaTTExp.Binder.Subst 𝕊 side mark using (MarkSub; MarkVar; tm[])
open import CaTTExp.Binder.Scoping 𝕊 side mark using (tm-sc; ty-sc; sub-sc)
open import CaTTExp.Binder.Deep 𝕊 side mark
open import CaTTExp.Binder.PureEmbed 𝕊 side mark using (SidePure)
open import CaTTExp.Binder.VCyl 𝕊 KF
open import CaTTExp.Binder.CylLaws 𝕊 KF using (dim-[]′; anyL-++)
open import CaTTExp.Binder.VWhisk 𝕊 side mark KF
open Laws 𝕊 using (Closed; BinderLaws)

------------------------------------------------------------------------
-- Arithmetic and syntax.

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  eq-sound : ∀ {i n} → (i ==ℕ n) ≡ true → i ≡ n
  eq-sound {i} {n} e = ==ℕ-sound i n (subst T (sym e) tt)

  lt-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  lt-ne zero    zero    _ ()
  lt-ne zero    (suc n) _ _ = tt
  lt-ne (suc i) zero    () _
  lt-ne (suc i) (suc n) p q = lt-ne i n p q

  ==-suc-dim : ∀ n → (n ==ℕ suc n) ≡ false
  ==-suc-dim zero    = refl
  ==-suc-dim (suc n) = ==-suc-dim n

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

baseAt-low : ∀ k A s u → T (k <ℕ suc (dim A)) → baseAt k (arr A s u) ≡ baseAt k A
baseAt-low k A s u p = if-f (<→≢ k (suc (dim A)) p)

tgtAt-top : ∀ A s u → tgtAt (dim A) (arr A s u) ≡ u
tgtAt-top A s u = if-t (==-self {dim A} refl)

tgtAt-low : ∀ k A s u → T (k <ℕ dim A) → tgtAt k (arr A s u) ≡ tgtAt k A
tgtAt-low k A s u p = if-f (<→≢ k (dim A) p)

srcAt-top : ∀ A s u → srcAt (dim A) (arr A s u) ≡ s
srcAt-top A s u = if-t (==-self {dim A} refl)

srcAt-low : ∀ k A s u → T (k <ℕ dim A) → srcAt k (arr A s u) ≡ srcAt k A
srcAt-low k A s u p = if-f (<→≢ k (dim A) p)

-- The top-dimensional type, source and target of a cell type.
tyK-top : ∀ k C s t → dim C ≡ k → baseAt k (arr C s t) ≡ C
tyK-top .(dim C) C s t refl = trans (if-f (==-suc-dim (dim C))) (baseAt-top C)

srcK-top : ∀ k C s t → dim C ≡ k → srcAt k (arr C s t) ≡ s
srcK-top .(dim C) C s t refl = srcAt-top C s t

tgtK-top : ∀ k C s t → dim C ≡ k → tgtAt k (arr C s t) ≡ t
tgtK-top .(dim C) C s t refl = tgtAt-top C s t

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

module Shape (D : Datum) where

  dim-TP : ∀ k A → T (k <ℕ suc (dim A)) → dim (TP D k A) ≡ dim A
  dim-TP zero    A           p = dim-[]′ A (mm D)
  dim-TP (suc k) ⋆           ()
  dim-TP (suc k) (arr A s u) p with k ==ℕ dim A in e
  ... | true  = cong suc (dim-TP k A p)
  ... | false = cong suc (dim-TP (suc k) A (lt-ne k (dim A) p e))

  dim-TL : ∀ k A → T (k <ℕ suc (dim A)) → dim (TL D k A) ≡ dim A
  dim-TL zero    A           p = dim-[]′ A (mp D)
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
  TP-top A s u = if-t (==-self {dim A} refl)

  TL-top : ∀ A s u → TL D (suc (dim A)) (arr A s u) ≡ arr (TP D (dim A) A) (P D (dim A) s A) (L D (dim A) u A)
  TL-top A s u = if-t (==-self {dim A} refl)

  TL≡TP : ∀ A → TL D (dim A) A ≡ TP D (dim A) A
  TL≡TP ⋆           = refl
  TL≡TP (arr A s u) = trans (TL-top A s u) (sym (TP-top A s u))

  -- The k-type and k-target of TP k A, the k-type and k-source of TL k A.
  tyK-TP : ∀ k A → T (k <ℕ dim A) → baseAt k (TP D k A) ≡ TP D k (baseAt k A)
  tyK-TP k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (baseAt k) (TP-low k A s u p))
    (trans (tyK-top k (TP D k A) (P D k s A) (P D k u A) (dim-TP k A p))
           (cong (TP D k) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (baseAt k) (TP-low k A s u p))
    (trans (baseAt-arr k (TP D k A) (P D k s A) (P D k u A) (subst (λ m → T (k <ℕ m)) (sym (dim-TP k A p)) q))
    (trans (tyK-TP k A q) (cong (TP D k) (sym (baseAt-low k A s u p)))))

  tgtK-TP : ∀ k A → T (k <ℕ dim A) → tgtAt k (TP D k A) ≡ P D k (tgtAt k A) (baseAt k A)
  tgtK-TP k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (tgtAt k) (TP-low k A s u p))
    (trans (tgtK-top k (TP D k A) (P D k s A) (P D k u A) (dim-TP k A p))
           (cong₂ (P D k) (sym (tgtAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (tgtAt k) (TP-low k A s u p))
    (trans (tgtAt-arr k (TP D k A) (P D k s A) (P D k u A) (subst (λ m → T (k <ℕ m)) (sym (dim-TP k A p)) q))
    (trans (tgtK-TP k A q) (cong₂ (P D k) (sym (tgtAt-low k A s u q)) (sym (baseAt-low k A s u p)))))

  tyK-TL : ∀ k A → T (k <ℕ dim A) → baseAt k (TL D k A) ≡ TP D k (baseAt k A)
  tyK-TL k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (baseAt k) (TL-low k A s u p))
    (trans (tyK-top k (TL D k A) (L D k s A) (L D k u A) (dim-TL k A p))
    (trans (TL≡TP A) (cong (TP D k) (sym (trans (baseAt-low k A s u p) (baseAt-top A))))))
  ... | low q =
    trans (cong (baseAt k) (TL-low k A s u p))
    (trans (baseAt-arr k (TL D k A) (L D k s A) (L D k u A) (subst (λ m → T (k <ℕ m)) (sym (dim-TL k A p)) q))
    (trans (tyK-TL k A q) (cong (TP D k) (sym (baseAt-low k A s u p)))))

  srcK-TL : ∀ k A → T (k <ℕ dim A) → srcAt k (TL D k A) ≡ L D k (srcAt k A) (baseAt k A)
  srcK-TL k (arr A s u) p with cmp k (dim A) p
  ... | top refl =
    trans (cong (srcAt k) (TL-low k A s u p))
    (trans (srcK-top k (TL D k A) (L D k s A) (L D k u A) (dim-TL k A p))
           (cong₂ (L D k) (sym (srcAt-top A s u)) (sym (trans (baseAt-low k A s u p) (baseAt-top A)))))
  ... | low q =
    trans (cong (srcAt k) (TL-low k A s u p))
    (trans (srcAt-arr k (TL D k A) (L D k s A) (L D k u A) (subst (λ m → T (k <ℕ m)) (sym (dim-TL k A p)) q))
    (trans (srcK-TL k A q) (cong₂ (L D k) (sym (srcAt-low k A s u q)) (sym (baseAt-low k A s u p)))))

  ----------------------------------------------------------------------
  -- The k-th whisker lands in TP (k+1) A, resp. TL (k+1) A.

  rw-ty : ∀ k A (p : T (k <ℕ dim A)) → touched D (tgtAt k A) ≡ true → ∀ c →
          embTy (Dv.wK k (dim A ∸ suc k)) [ σR c (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A)) ]ty
            ≡ TP D (suc k) A
  rw-ty k (arr A s u) p e c with cmp k (dim A) p
  ... | top refl =
    trans (cong (λ j → embTy (Dv.wK k j) [ σR c C z h ]ty) (n∸n k))
    (trans (rwT-ty0 k c C z h (dim-TP k (arr A s u) (<-suc k (suc (dim A)) p)))
    (trans (cong₃ arr (trans (cong (baseAt k) (TP-low k A s u p)) (tyK-top k (TP D k A) (P D k s A) (P D k u A) (dim-TP k A p)))
                      (trans (cong (srcAt k) (TP-low k A s u p)) (srcK-top k (TP D k A) (P D k s A) (P D k u A) (dim-TP k A p)))
                      (cong₂ (L D k) (tgtAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A))))
           (sym (TP-top A s u))))
    where
    C = TP D k (arr A s u)
    z = L D k (tgtAt k (arr A s u)) (baseAt k (arr A s u))
    h = cyl D (tgtAt k (arr A s u))
  ... | low q =
    trans (cong₂ (λ w B → embTy (Dv.wK k (dim A ∸ k)) [ σR c (TP D k (arr A s u)) (L D k w B) (cyl D w) ]ty)
                 (tgtAt-low k A s u q) (baseAt-low k A s u p))
    (trans (cong (λ j → embTy (Dv.wK k j) [ σR c (TP D k (arr A s u)) z h ]ty) (∸-suc k (dim A) q))
    (trans (cong (λ C → embTy (Dv.wK k (suc j)) [ σR c C z h ]ty) (TP-low k A s u p))
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
          embTy (Dv.lK k (dim A ∸ suc k))
            [ σL k (dim A ∸ suc k) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) c (TL D k A) ]ty
            ≡ TL D (suc k) A
  lw-ty k (arr A s u) p e c with cmp k (dim A) p
  ... | top refl =
    trans (cong (λ j → embTy (Dv.lK k j) [ σL k j h x c C ]ty) (n∸n k))
    (trans (lwT-ty0 k h x c C (dim-TL k (arr A s u) (<-suc k (suc (dim A)) p)))
    (trans (cong₃ arr (trans (cong (baseAt k) (TL-low k A s u p))
                        (trans (tyK-top k (TL D k A) (L D k s A) (L D k u A) (dim-TL k A p)) (TL≡TP A)))
                      (cong₂ (P D k) (srcAt-top A s u) (trans (baseAt-low k A s u p) (baseAt-top A)))
                      (trans (cong (tgtAt k) (TL-low k A s u p)) (tgtK-top k (TL D k A) (L D k s A) (L D k u A) (dim-TL k A p))))
           (sym (TL-top A s u))))
    where
    C = TL D k (arr A s u)
    x = P D k (srcAt k (arr A s u)) (baseAt k (arr A s u))
    h = cyl D (srcAt k (arr A s u))
  ... | low q =
    trans (cong₂ (λ w B → embTy (Dv.lK k (dim A ∸ k)) [ σL k (dim A ∸ k) (cyl D w) (P D k w B) c (TL D k (arr A s u)) ]ty)
                 (srcAt-low k A s u q) (baseAt-low k A s u p))
    (trans (cong (λ m → embTy (Dv.lK k m) [ σL k m h x c (TL D k (arr A s u)) ]ty) (∸-suc k (dim A) q))
    (trans (cong (λ C → embTy (Dv.lK k (suc j)) [ σL k (suc j) h x c C ]ty) (TL-low k A s u p))
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

module Bd (closed : Closed) (laws : BinderLaws) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar)
          (sp : SidePure) where
  open Typed closed laws mren msub mvar sp

  -- A datum with typed copies; unselected variables have equal copies,
  -- and untouched terms have untouched types.
  record BaseD (D : Datum) (Γ Δ : Ctx) : Set where
    field
      bmm   : Δ ⊢sub mm D ∶ Γ
      bmp   : Δ ⊢sub mp D ∶ Γ
      bsame : ∀ x → T (x <ℕ len Γ) → sel D x ≡ false → lookupₛ (mm D) x ≡ lookupₛ (mp D) x
      but   : ∀ {t A} → Γ ⊢tm t ∶ A → touched D t ≡ false → anyL (sel D) (fvTy A) ≡ false

  -- Cylinders of the touched iterated boundaries of a type.
  module _ (D : Datum) (Δ : Ctx) where
    CylT : Tm → Ty → Set
    CylT t A = T (touched D t) → DTm Δ (cyl D t) (cylTy D t A)

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
    open Shape D

    private
      split : ∀ xs ys → anyL (sel D) (xs ++ ys) ≡ false → (anyL (sel D) xs ≡ false) × (anyL (sel D) ys ≡ false)
      split xs ys e = let e' = trans (sym (anyL-++ (sel D) xs ys)) e in ∨-false-l e' , ∨-false-r e'

    mutual
      same-tm : ∀ t → T (scTm? (len Γ) t) → touched D t ≡ false → t [ mm D ]tm ≡ t [ mp D ]tm
      same-tm (var x)       p e = bsame x p (∨-false-l e)
      same-tm (bvar _ _)    p e = refl
      same-tm (coh Q B γ)   p e = cong (coh Q B) (same-sub γ p e)
      same-tm (cst _)       p e = refl
      same-tm (bnd b y Θ γ) p e =
        cong₂ (bnd b y) (same-tel Θ (fst pp) (fst ee)) (same-sub γ (snd pp) (snd ee))
        where pp = T∧ {scTel? (len Γ) Θ} p
              ee = split (fvTel Θ) (fvSub γ) e

      same-sub : ∀ γ → T (scSub? (len Γ) γ) → anyL (sel D) (fvSub γ) ≡ false → γ ∘ mm D ≡ γ ∘ mp D
      same-sub ⟨⟩       p e = refl
      same-sub (γ ,ₛ t) p e =
        cong₂ _,ₛ_ (same-sub γ (fst pp) (fst ee)) (same-tm t (snd pp) (snd ee))
        where pp = T∧ {scSub? (len Γ) γ} p
              ee = split (fvSub γ) (fvTm t) e

      same-tel : ∀ Θ → T (scTel? (len Γ) Θ) → anyL (sel D) (fvTel Θ) ≡ false → Θ [ mm D ]tel ≡ Θ [ mp D ]tel
      same-tel ε              p e = refl
      same-tel (Θ ▸[ ms ] A) p e =
        cong₂ (_▸[ ms ]_) (same-tel Θ (fst pp) (fst ee)) (same-ty A (snd pp) (snd ee))
        where pp = T∧ {scTel? (len Γ) Θ} p
              ee = split (fvTel Θ) (fvTy A) e

      same-ty : ∀ A → T (scTy? (len Γ) A) → anyL (sel D) (fvTy A) ≡ false → A [ mm D ]ty ≡ A [ mp D ]ty
      same-ty ⋆           p e = refl
      same-ty (arr A s u) p e =
        cong₃ arr (same-ty A (fst pp) (fst ee)) (same-tm s (fst qq) (fst ff)) (same-tm u (snd qq) (snd ff))
        where pp = T∧ {scTy? (len Γ) A} p
              qq = T∧ {scTm? (len Γ) s} (snd pp)
              ee = split (fvTy A) (fvTm s ++ fvTm u) e
              ff = split (fvTm s) (fvTm u) (snd ee)

    -- The two whiskered copies of an untouched boundary agree.
    triv : ∀ {w B} → Γ ⊢tm w ∶ B → touched D w ≡ false → ∀ k → dim B ≡ k →
           P D k w B ≡ L D k w B
    triv {w} {B} dw e k eB =
      trans (triv-P w B uB k le)
      (trans (same-tm w (tm-sc closed laws dw) e) (sym (triv-L w B uB k le)))
      where
      uB = but dw e
      le = subst (λ m → T (k <ℕ suc m)) (sym eB) (n<sn k)

    private
      cylTy-k : ∀ {w B} k → dim B ≡ k → cylTy D w B ≡ arr (TP D k B) (P D k w B) (L D k w B)
      cylTy-k {w} {B} k eB = cong (λ m → arr (TP D m B) (P D m w B) (L D m w B)) eB

    module _ {t A} (dt : DTm Γ t A) (b : CylBd D Δ A) where
      private
        dA = snd dt

      stepP : ∀ k (p : T (k <ℕ dim A)) v → touched D (tgtAt k A) ≡ v →
              DTm Δ (P D k t A) (TP D k A) →
              DTm Δ (rwI k (dim A) (P D k t A) (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A)) v)
                    (TP D (suc k) A)
      stepP k p true e d =
        subst (DTm Δ (rwT k (dim A ∸ suc k) (P D k t A) (TP D k A) (L D k (tgtAt k A) (baseAt k A)) (cyl D (tgtAt k A))))
          (rw-ty k A p e (P D k t A))
          (rwT-wf k (dim A ∸ suc k) (trans (dim-TP k A (<-suc k (dim A) p)) (nB-sub k (dim A) p)) d
            (subst (DTm Δ (cyl D w))
               (trans (cylTy-k k (dim-baseAt k A (<-suc k (dim A) p)))
                      (cong₂ (λ X y → arr X y (L D k w W)) (sym (tyK-TP k A p)) (sym (tgtK-TP k A p))))
               (bd-tgt k A b p (subst T (sym e) tt))))
        where
        w = tgtAt k A
        W = baseAt k A
      stepP k p false e d =
        subst (DTm Δ (P D k t A))
          (rw-omit k A p e (triv (fst (snd (bdry-wf k A p dA))) e k (dim-baseAt k A (<-suc k (dim A) p)))) d

      stepL : ∀ k (p : T (k <ℕ dim A)) v → touched D (srcAt k A) ≡ v →
              DTm Δ (L D k t A) (TL D k A) →
              DTm Δ (lwI k (dim A) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) (L D k t A) (TL D k A) v)
                    (TL D (suc k) A)
      stepL k p true e d =
        subst (DTm Δ (lwT k (dim A ∸ suc k) (cyl D (srcAt k A)) (P D k (srcAt k A) (baseAt k A)) (L D k t A) (TL D k A)))
          (lw-ty k A p e (L D k t A))
          (lwT-wf k (dim A ∸ suc k) d (trans (dim-TL k A (<-suc k (dim A) p)) (nB-sub k (dim A) p))
            (subst (DTm Δ (cyl D w))
               (trans (cylTy-k k (dim-baseAt k A (<-suc k (dim A) p)))
                      (cong₂ (λ X y → arr X (P D k w W) y) (sym (tyK-TL k A p)) (sym (srcK-TL k A p))))
               (bd-src k A b p (subst T (sym e) tt))))
        where
        w = srcAt k A
        W = baseAt k A
      stepL k p false e d =
        subst (DTm Δ (L D k t A))
          (lw-omit k A p e (sym (triv (fst (fst (bdry-wf k A p dA))) e k (dim-baseAt k A (<-suc k (dim A) p))))) d

      P-wf : ∀ k → T (k <ℕ suc (dim A)) → DTm Δ (P D k t A) (TP D k A)
      P-wf zero    p = tm[] closed laws mren msub mvar (fst dt) bmm , dty[] closed laws mren msub mvar A dA bmm
      P-wf (suc k) p = stepP k p (touched D (tgtAt k A)) refl (P-wf k (<-suc k (dim A) p))

      L-wf : ∀ k → T (k <ℕ suc (dim A)) → DTm Δ (L D k t A) (TL D k A)
      L-wf zero    p = tm[] closed laws mren msub mvar (fst dt) bmp , dty[] closed laws mren msub mvar A dA bmp
      L-wf (suc k) p = stepL k p (touched D (srcAt k A)) refl (L-wf k (<-suc k (dim A) p))

      -- a_t → b_t is a well-formed (deep) type of Δ.
      aT-wf : DTm Δ (aT D t A) (TP D (dim A) A)
      aT-wf = P-wf (dim A) (n<sn (dim A))

      bT-wf : DTm Δ (bT D t A) (TP D (dim A) A)
      bT-wf = subst (DTm Δ (bT D t A)) (TL≡TP A) (L-wf (dim A) (n<sn (dim A)))

      cylTy-wf : DTy Δ (cylTy D t A)
      cylTy-wf = snd aT-wf , fst aT-wf , fst bT-wf

  ----------------------------------------------------------------------
  -- Suffix selections: every variable from n on. An untouched term is
  -- scoped below n, and so is its type (by scoping alone, as in
  -- Scoping.tm-ty-sc, with res-sc at n), so its type is untouched.

  module Suffix (n : Nat) where
    suf : Nat → Bool
    suf x = not (x <ℕ n)

    private
      nf : ∀ b → not b ≡ false → T b
      nf true _ = tt

      tn : ∀ b → T b → not b ≡ false
      tn true _ = refl

      join : ∀ xs ys → anyL suf xs ≡ false → anyL suf ys ≡ false → anyL suf (xs ++ ys) ≡ false
      join xs ys a b = trans (anyL-++ suf xs ys) (cong₂ _∨_ a b)

      split' : ∀ xs ys → anyL suf (xs ++ ys) ≡ false → (anyL suf xs ≡ false) × (anyL suf ys ≡ false)
      split' xs ys e = let e' = trans (sym (anyL-++ suf xs ys)) e in ∨-false-l e' , ∨-false-r e'

      scTy-le : ∀ m k A → T (m <ℕ suc k) → T (scTy? m A) → T (scTy? k A)
      scTy-le zero    zero    A p a = a
      scTy-le (suc m) zero    A () a
      scTy-le m       (suc k) A p a with m ==ℕ suc k in e
      ... | true  = subst (λ x → T (scTy? x A)) (eq-sound {m} {suc k} e) a
      ... | false = scTy-suc A (scTy-le m k A (lt-ne m (suc k) p e) a)

    -- The type of entry i is scoped below i.
    lookup-sc : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → T (scTy? i A)
    lookup-sc {Γ ▸[ _ ] B} {i} {A} (▸-wf w b) eq with i ==ℕ len Γ in e
    ... | true  = subst₂ (λ x X → T (scTy? x X)) (sym (eq-sound {i} {len Γ} e)) (just-inj eq) (ty-sc closed laws b)
    ... | false = lookup-sc w eq

    mutual
      un-sc-tm : ∀ t → anyL suf (fvTm t) ≡ false → T (scTm? n t)
      un-sc-tm (var x)       e = nf (x <ℕ n) (∨-false-l e)
      un-sc-tm (bvar _ _)    e = tt
      un-sc-tm (coh _ _ σ)   e = un-sc-sub σ e
      un-sc-tm (cst _)       e = tt
      un-sc-tm (bnd _ _ Θ σ) e = let (a , b) = split' (fvTel Θ) (fvSub σ) e in ∧T (un-sc-tel Θ a) (un-sc-sub σ b)

      un-sc-sub : ∀ σ → anyL suf (fvSub σ) ≡ false → T (scSub? n σ)
      un-sc-sub ⟨⟩       e = tt
      un-sc-sub (σ ,ₛ t) e = let (a , b) = split' (fvSub σ) (fvTm t) e in ∧T (un-sc-sub σ a) (un-sc-tm t b)

      un-sc-tel : ∀ Θ → anyL suf (fvTel Θ) ≡ false → T (scTel? n Θ)
      un-sc-tel ε              e = tt
      un-sc-tel (Θ ▸[ _ ] A) e = let (a , b) = split' (fvTel Θ) (fvTy A) e in ∧T (un-sc-tel Θ a) (un-sc-ty A b)

      un-sc-ty : ∀ A → anyL suf (fvTy A) ≡ false → T (scTy? n A)
      un-sc-ty ⋆           e = tt
      un-sc-ty (arr A s u) e =
        let (a , bc) = split' (fvTy A) (fvTm s ++ fvTm u) e
            (b , c)  = split' (fvTm s) (fvTm u) bc
        in ∧T (un-sc-ty A a) (∧T (un-sc-tm s b) (un-sc-tm u c))

    mutual
      sc-un-tm : ∀ t → T (scTm? n t) → anyL suf (fvTm t) ≡ false
      sc-un-tm (var x)       p = cong (_∨ false) (tn (x <ℕ n) p)
      sc-un-tm (bvar _ _)    p = refl
      sc-un-tm (coh _ _ σ)   p = sc-un-sub σ p
      sc-un-tm (cst _)       p = refl
      sc-un-tm (bnd _ _ Θ σ) p = let (a , b) = T∧ {scTel? n Θ} p in join (fvTel Θ) (fvSub σ) (sc-un-tel Θ a) (sc-un-sub σ b)

      sc-un-sub : ∀ σ → T (scSub? n σ) → anyL suf (fvSub σ) ≡ false
      sc-un-sub ⟨⟩       p = refl
      sc-un-sub (σ ,ₛ t) p = let (a , b) = T∧ {scSub? n σ} p in join (fvSub σ) (fvTm t) (sc-un-sub σ a) (sc-un-tm t b)

      sc-un-tel : ∀ Θ → T (scTel? n Θ) → anyL suf (fvTel Θ) ≡ false
      sc-un-tel ε              p = refl
      sc-un-tel (Θ ▸[ _ ] A) p = let (a , b) = T∧ {scTel? n Θ} p in join (fvTel Θ) (fvTy A) (sc-un-tel Θ a) (sc-un-ty A b)

      sc-un-ty : ∀ A → T (scTy? n A) → anyL suf (fvTy A) ≡ false
      sc-un-ty ⋆           p = refl
      sc-un-ty (arr A s u) p =
        let (a , bc) = T∧ {scTy? n A} p
            (b , c)  = T∧ {scTm? n s} bc
        in join (fvTy A) (fvTm s ++ fvTm u) (sc-un-ty A a) (join (fvTm s) (fvTm u) (sc-un-tm s b) (sc-un-tm u c))

    -- A term scoped below n has its type scoped below n.
    ty-below : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (scTm? n t) → T (scTy? n A)
    ty-below (var-wf {i} {A} w eq) p = scTy-le i n A (<-suc i n p) (lookup-sc w eq)
    ty-below (coh-wf {A = A} {t} {u} {σ} _ _ a _ s) p =
      sc-ty[] (arr A t u) σ (subst (λ m → T (scTy? m (arr A t u))) (sym (snd (sub-sc closed laws s))) (ty-sc closed laws a)) p
    ty-below (cst-wf {k} _ _) p = scTy-mono n (ty k) (closed k)
    ty-below (bnd-wf {b} {y} {Θ} {ts} sc _ _ ok as) p =
      let (a , c) = T∧ {scTel? n Θ} p in sc-opTy 0 ts (bres b y Θ) c (BinderLaws.res-sc laws b y Θ n ok a)

    -- `but` for a suffix selection.
    but-suffix : ∀ {Γ t A} (D : Datum) → (∀ x → sel D x ≡ suf x) →
                 Γ ⊢tm t ∶ A → touched D t ≡ false → anyL (sel D) (fvTy A) ≡ false
    but-suffix {t = t} {A} D es dt e =
      trans (anyL-ext (sel D) suf es (fvTy A))
            (sc-un-ty A (ty-below dt (un-sc-tm t (trans (sym (anyL-ext (sel D) suf es (fvTm t))) e))))
      where
      anyL-ext : ∀ f g → (∀ x → f x ≡ g x) → ∀ xs → anyL f xs ≡ anyL g xs
      anyL-ext f g h []       = refl
      anyL-ext f g h (x ∷ xs) = cong₂ _∨_ (h x) (anyL-ext f g h xs)
