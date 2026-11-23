------------------------------------------------------------------------
-- No CaTT 3-cell connects g ∗₁ h and h ∗₁ g in
-- Γ = (x, y, f : x → y, g h : f ⇒ f)  (ledger S20 (i), stage 3f).
--
-- So Theorem A needs a hypothesis such as Key2 (CaTTExp.RCProc.
-- TwoPathCtx): g ∗₁ h and h ∗₁ g have the same strict image (`gh≈hg`), yet
-- relative coherence must not answer the query.
--
-- The model argument. `Endo` is a strict ω-category (CaTTExp.Strict.
-- Omega) with 0-cells x, y, one 1-cell f : x → y, the 2-cells f ⇒ f
-- the words over Bool (vertical composition is concatenation, the
-- identity of f is the empty word), and nothing above dimension 2.
-- CaTT is sound in every strict ω-category (CaTTExp.Strict.OmegaSound.
-- sound-in). A 3-cell w : g ∗₁ h ⇒ h ∗₁ g would denote a cell c whose
-- 2-source and 2-target are the denotations of g ∗₁ h and h ∗₁ g. In
-- `Endo` every cell is its own 2-source and 2-target, so both would be
-- c. With g ↦ [true] and h ↦ [false] they are [true, false] and
-- [false, true], which differ (`no-3cell`).
------------------------------------------------------------------------
module CaTTExp.RCProc.TwoPathModel where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree ∅ using (tr)
open import CaTTExp.RCProc.TwoPathFacts using (Γgh)

------------------------------------------------------------------------
-- The strict ω-category.

data Cell : Set where
  X Y : Cell
  F   : List Bool → Cell

private
  ++-[] : ∀ (w : List Bool) → w ++ [] ≡ w
  ++-[] []      = refl
  ++-[] (b ∷ w) = cong (b ∷_) (++-[] w)

  ++-as : ∀ (u v w : List Bool) → (u ++ v) ++ w ≡ u ++ (v ++ w)
  ++-as []      v w = refl
  ++-as (b ∷ u) v w = cong (b ∷_) (++-as u v w)

sr tg : Nat → Cell → Cell
sr n X = X
sr n Y = Y
sr zero          (F w) = X
sr (suc zero)    (F w) = F []
sr (suc (suc n)) (F w) = F w
tg n X = X
tg n Y = Y
tg zero          (F w) = Y
tg (suc zero)    (F w) = F []
tg (suc (suc n)) (F w) = F w

join0 : Cell → Cell → Cell
join0 X b = b
join0 a _ = a

join1 : Cell → Cell → Cell
join1 (F u) (F v) = F (u ++ v)
join1 a     _     = a

cmp : ∀ n (a b : Cell) → tg n a ≡ sr n b → Cell
cmp zero          a b _ = join0 a b
cmp (suc zero)    a b _ = join1 a b
cmp (suc (suc n)) a b _ = a

private
  -- Above dimension 1 every cell is its own boundary.
  sr2 : ∀ n c → sr (suc (suc n)) c ≡ c
  sr2 n X = refl
  sr2 n Y = refl
  sr2 n (F w) = refl
  tg2 : ∀ n c → tg (suc (suc n)) c ≡ c
  tg2 n X = refl
  tg2 n Y = refl
  tg2 n (F w) = refl

  eq2 : ∀ n {a b} → tg (suc (suc n)) a ≡ sr (suc (suc n)) b → a ≡ b
  eq2 n {a} {b} p = trans (sym (tg2 n a)) (trans p (sr2 n b))

  F≢X : ∀ {w} → F w ≡ X → ⊥
  F≢X ()

-- (i) boundaries of boundaries.
private
  ss< : ∀ {m n} x → m < n → sr m (sr n x) ≡ sr m x
  ss< X _ = refl
  ss< Y _ = refl
  ss< {zero}  {suc zero}    (F w) _ = refl
  ss< {zero}  {suc (suc n)} (F w) _ = refl
  ss< {suc zero} {suc (suc n)} (F w) _ = refl
  ss< {suc (suc m)} {suc (suc n)} (F w) _ = refl
  ss< {suc zero} {suc zero} (F w) (s≤s ())
  ss< {suc (suc m)} {suc zero} (F w) (s≤s ())
  ss< {_} {zero} (F w) ()

  st< : ∀ {m n} x → m < n → sr m (tg n x) ≡ sr m x
  st< X _ = refl
  st< Y _ = refl
  st< {zero}  {suc zero}    (F w) _ = refl
  st< {zero}  {suc (suc n)} (F w) _ = refl
  st< {suc zero} {suc (suc n)} (F w) _ = refl
  st< {suc (suc m)} {suc (suc n)} (F w) _ = refl
  st< {suc zero} {suc zero} (F w) (s≤s ())
  st< {suc (suc m)} {suc zero} (F w) (s≤s ())
  st< {_} {zero} (F w) ()

  ts< : ∀ {m n} x → m < n → tg m (sr n x) ≡ tg m x
  ts< X _ = refl
  ts< Y _ = refl
  ts< {zero}  {suc zero}    (F w) _ = refl
  ts< {zero}  {suc (suc n)} (F w) _ = refl
  ts< {suc zero} {suc (suc n)} (F w) _ = refl
  ts< {suc (suc m)} {suc (suc n)} (F w) _ = refl
  ts< {suc zero} {suc zero} (F w) (s≤s ())
  ts< {suc (suc m)} {suc zero} (F w) (s≤s ())
  ts< {_} {zero} (F w) ()

  tt< : ∀ {m n} x → m < n → tg m (tg n x) ≡ tg m x
  tt< X _ = refl
  tt< Y _ = refl
  tt< {zero}  {suc zero}    (F w) _ = refl
  tt< {zero}  {suc (suc n)} (F w) _ = refl
  tt< {suc zero} {suc (suc n)} (F w) _ = refl
  tt< {suc (suc m)} {suc (suc n)} (F w) _ = refl
  tt< {suc zero} {suc zero} (F w) (s≤s ())
  tt< {suc (suc m)} {suc zero} (F w) (s≤s ())
  tt< {_} {zero} (F w) ()

  ss≥ : ∀ {m n} x → n ≤ m → sr m (sr n x) ≡ sr n x
  ss≥ X _ = refl
  ss≥ Y _ = refl
  ss≥ {m} {zero} (F w) _ = refl
  ss≥ {suc zero} {suc zero} (F w) _ = refl
  ss≥ {suc (suc m)} {suc zero} (F w) _ = refl
  ss≥ {suc (suc m)} {suc (suc n)} (F w) _ = refl
  ss≥ {zero} {suc n} (F w) ()
  ss≥ {suc zero} {suc (suc n)} (F w) (s≤s ())

  ts≥ : ∀ {m n} x → n ≤ m → tg m (sr n x) ≡ sr n x
  ts≥ X _ = refl
  ts≥ Y _ = refl
  ts≥ {m} {zero} (F w) _ = refl
  ts≥ {suc zero} {suc zero} (F w) _ = refl
  ts≥ {suc (suc m)} {suc zero} (F w) _ = refl
  ts≥ {suc (suc m)} {suc (suc n)} (F w) _ = refl
  ts≥ {zero} {suc n} (F w) ()
  ts≥ {suc zero} {suc (suc n)} (F w) (s≤s ())

  st≥ : ∀ {m n} x → n ≤ m → sr m (tg n x) ≡ tg n x
  st≥ X _ = refl
  st≥ Y _ = refl
  st≥ {m} {zero} (F w) _ = refl
  st≥ {suc zero} {suc zero} (F w) _ = refl
  st≥ {suc (suc m)} {suc zero} (F w) _ = refl
  st≥ {suc (suc m)} {suc (suc n)} (F w) _ = refl
  st≥ {zero} {suc n} (F w) ()
  st≥ {suc zero} {suc (suc n)} (F w) (s≤s ())

  tt≥ : ∀ {m n} x → n ≤ m → tg m (tg n x) ≡ tg n x
  tt≥ X _ = refl
  tt≥ Y _ = refl
  tt≥ {m} {zero} (F w) _ = refl
  tt≥ {suc zero} {suc zero} (F w) _ = refl
  tt≥ {suc (suc m)} {suc zero} (F w) _ = refl
  tt≥ {suc (suc m)} {suc (suc n)} (F w) _ = refl
  tt≥ {zero} {suc n} (F w) ()
  tt≥ {suc zero} {suc (suc n)} (F w) (s≤s ())

-- (iii) boundaries of composites.
private
  s-c : ∀ n x y p → sr n (cmp n x y p) ≡ sr n x
  s-c zero X y p = sym p
  s-c zero Y y p = refl
  s-c zero (F w) y p = refl
  s-c (suc zero) X y p = refl
  s-c (suc zero) Y y p = refl
  s-c (suc zero) (F u) (F v) p = refl
  s-c (suc zero) (F u) X ()
  s-c (suc zero) (F u) Y ()
  s-c (suc (suc n)) x y p = refl

  t-c : ∀ n x y p → tg n (cmp n x y p) ≡ tg n y
  t-c zero X y p = refl
  t-c zero Y Y p = refl
  t-c zero Y X ()
  t-c zero Y (F w) ()
  t-c zero (F u) Y p = refl
  t-c zero (F u) X ()
  t-c zero (F u) (F v) ()
  t-c (suc zero) X X p = refl
  t-c (suc zero) X Y ()
  t-c (suc zero) X (F v) ()
  t-c (suc zero) Y Y p = refl
  t-c (suc zero) Y X ()
  t-c (suc zero) Y (F v) ()
  t-c (suc zero) (F u) (F v) p = refl
  t-c (suc zero) (F u) X ()
  t-c (suc zero) (F u) Y ()
  t-c (suc (suc n)) x y p = trans (tg2 n x) (trans (eq2 n p) (sym (tg2 n y)))

  s-c< : ∀ {m n} x y p → m < n → sr m (cmp n x y p) ≡ sr m x
  s-c< {zero} {suc zero} X y p _ = refl
  s-c< {zero} {suc zero} Y y p _ = refl
  s-c< {zero} {suc zero} (F u) (F v) p _ = refl
  s-c< {zero} {suc zero} (F u) X () _
  s-c< {zero} {suc zero} (F u) Y () _
  s-c< {m} {suc (suc n)} x y p _ = refl
  s-c< {suc m} {suc zero} x y p (s≤s ())
  s-c< {m} {zero} x y p ()

  t-c< : ∀ {m n} x y p → m < n → tg m (cmp n x y p) ≡ tg m y
  t-c< {zero} {suc zero} X X p _ = refl
  t-c< {zero} {suc zero} X Y () _
  t-c< {zero} {suc zero} X (F v) () _
  t-c< {zero} {suc zero} Y Y p _ = refl
  t-c< {zero} {suc zero} Y X () _
  t-c< {zero} {suc zero} Y (F v) () _
  t-c< {zero} {suc zero} (F u) (F v) p _ = refl
  t-c< {zero} {suc zero} (F u) X () _
  t-c< {zero} {suc zero} (F u) Y () _
  t-c< {m} {suc (suc n)} x y p _ = cong (tg m) (eq2 n p)
  t-c< {suc m} {suc zero} x y p (s≤s ())
  t-c< {m} {zero} x y p ()

  s-c> : ∀ {m n} x y p → n < m → ∀ q → sr m (cmp n x y p) ≡ cmp n (sr m x) (sr m y) q
  s-c> {suc zero} {zero} X y p _ q = refl
  s-c> {suc zero} {zero} Y y p _ q = refl
  s-c> {suc zero} {zero} (F u) y p _ q = refl
  s-c> {suc (suc m)} {zero} X y p _ q = refl
  s-c> {suc (suc m)} {zero} Y y p _ q = refl
  s-c> {suc (suc m)} {zero} (F u) y p _ q = refl
  s-c> {suc (suc m)} {suc zero} X y p _ q = refl
  s-c> {suc (suc m)} {suc zero} Y y p _ q = refl
  s-c> {suc (suc m)} {suc zero} (F u) (F v) p _ q = refl
  s-c> {suc (suc m)} {suc zero} (F u) X () _ q
  s-c> {suc (suc m)} {suc zero} (F u) Y () _ q
  s-c> {suc (suc m)} {suc (suc n)} x y p _ q = refl
  s-c> {zero} {n} x y p () q
  s-c> {suc zero} {suc n} x y p (s≤s ()) q

  t-c> : ∀ {m n} x y p → n < m → ∀ q → tg m (cmp n x y p) ≡ cmp n (tg m x) (tg m y) q
  t-c> {suc zero} {zero} X X p _ q = refl
  t-c> {suc zero} {zero} X Y p _ q = refl
  t-c> {suc zero} {zero} X (F v) p _ q = refl
  t-c> {suc zero} {zero} Y y p _ q = refl
  t-c> {suc zero} {zero} (F u) y p _ q = refl
  t-c> {suc (suc m)} {zero} X y p _ q = refl
  t-c> {suc (suc m)} {zero} Y y p _ q = refl
  t-c> {suc (suc m)} {zero} (F u) y p _ q = refl
  t-c> {suc (suc m)} {suc zero} X y p _ q = refl
  t-c> {suc (suc m)} {suc zero} Y y p _ q = refl
  t-c> {suc (suc m)} {suc zero} (F u) (F v) p _ q = refl
  t-c> {suc (suc m)} {suc zero} (F u) X () _ q
  t-c> {suc (suc m)} {suc zero} (F u) Y () _ q
  t-c> {suc (suc m)} {suc (suc n)} x y p _ q = refl
  t-c> {zero} {n} x y p () q
  t-c> {suc zero} {suc n} x y p (s≤s ()) q

-- (iv) units, (v) associativity, (vi) interchange.
private
  u-l : ∀ n x p → cmp n (sr n x) x p ≡ x
  u-l zero X p = refl
  u-l zero Y p = refl
  u-l zero (F w) p = refl
  u-l (suc zero) X p = refl
  u-l (suc zero) Y p = refl
  u-l (suc zero) (F w) p = refl
  u-l (suc (suc n)) x p = sr2 n x

  u-r : ∀ n x p → cmp n x (tg n x) p ≡ x
  u-r zero X p = refl
  u-r zero Y p = refl
  u-r zero (F w) p = refl
  u-r (suc zero) X p = refl
  u-r (suc zero) Y p = refl
  u-r (suc zero) (F w) p = cong F (++-[] w)
  u-r (suc (suc n)) x p = refl

  as : ∀ n x y z p q p′ q′ → cmp n (cmp n x y p) z q ≡ cmp n x (cmp n y z p′) q′
  as zero X y z p q p′ q′ = refl
  as zero Y y z p q p′ q′ = refl
  as zero (F w) y z p q p′ q′ = refl
  as (suc zero) X y z p q p′ q′ = refl
  as (suc zero) Y y z p q p′ q′ = refl
  as (suc zero) (F u) (F v) (F w) p q p′ q′ = cong F (++-as u v w)
  as (suc zero) (F u) (F v) X p () p′ q′
  as (suc zero) (F u) (F v) Y p () p′ q′
  as (suc zero) (F u) X z () q p′ q′
  as (suc zero) (F u) Y z () q p′ q′
  as (suc (suc n)) x y z p q p′ q′ = refl

  ic : ∀ {m n} x y z w → m < n → ∀ p q r r₁ r₂ r₃ →
       cmp m (cmp n x y p) (cmp n z w q) r ≡ cmp n (cmp m x z r₁) (cmp m y w r₂) r₃
  ic {m} {suc (suc n)} x y z w _ p q r r₁ r₂ r₃ = cong (cmp m x z) (uip r r₁)
  -- m = 0, n = 1
  ic {zero} {suc zero} X X z w _ p q r r₁ r₂ r₃ = refl
  ic {zero} {suc zero} X Y z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} X (F v) z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} Y Y z w _ p q r r₁ r₂ r₃ = refl
  ic {zero} {suc zero} Y X z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} Y (F v) z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} (F u) X z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} (F u) Y z w _ () q r r₁ r₂ r₃
  ic {zero} {suc zero} (F u) (F v) Y Y _ p q r r₁ r₂ r₃ = refl
  ic {zero} {suc zero} (F u) (F v) Y X _ p () r r₁ r₂ r₃
  ic {zero} {suc zero} (F u) (F v) Y (F _) _ p () r r₁ r₂ r₃
  ic {zero} {suc zero} (F u) (F v) X w _ p q () r₁ r₂ r₃
  ic {zero} {suc zero} (F u) (F v) (F _) w _ p q r () r₂ r₃
  ic {suc m} {suc zero} x y z w (s≤s ()) p q r r₁ r₂ r₃
  ic {m} {zero} x y z w () p q r r₁ r₂ r₃

Endo : ωCat
Endo = record
  { C = Cell ; src = sr ; tgt = tg ; comp = cmp
  ; src-src-< = ss< ; src-tgt-< = st< ; tgt-src-< = ts< ; tgt-tgt-< = tt<
  ; src-src-≥ = ss≥ ; tgt-src-≥ = ts≥ ; src-tgt-≥ = st≥ ; tgt-tgt-≥ = tt≥
  ; src-comp = s-c ; tgt-comp = t-c ; src-comp-< = s-c< ; tgt-comp-< = t-c<
  ; src-comp-> = s-c> ; tgt-comp-> = t-c>
  ; unit-l = u-l ; unit-r = u-r ; assoc = as ; interchange = ic }

------------------------------------------------------------------------
-- The terms g ∗₁ h and h ∗₁ g in Γgh (x, y, f, g, h = 0, 1, 2, 3, 4).

-- Two vertically composable 2-cells: x, y, f, g, α : f ⇒ g, h, β : g ⇒ h.
V : Ctx
V = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ arr ⋆ (var 0) (var 1)
      ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 3) ▸ arr ⋆ (var 0) (var 1)
      ▸ arr (arr ⋆ (var 0) (var 1)) (var 3) (var 5)

vc : Tm → Tm → Tm
vc a b = coh V (arr (arr ⋆ (var 0) (var 1)) (var 2) (var 5))
           ⟪ var 0 ∷ var 1 ∷ var 2 ∷ var 2 ∷ a ∷ var 2 ∷ b ∷ [] ⟫

ffTy : Ty
ffTy = arr (arr ⋆ (var 0) (var 1)) (var 2) (var 2)

gh hg : Tm
gh = vc (var 3) (var 4)
hg = vc (var 4) (var 3)

-- Both are well typed (by the certified checker).
gh-wf : Γgh ⊢tm gh ∶ ffTy
gh-wf = snd (from-just (infer Γgh gh))

hg-wf : Γgh ⊢tm hg ∶ ffTy
hg-wf = snd (from-just (infer Γgh hg))

------------------------------------------------------------------------
-- The model argument.

private
  M0 : K → Cell
  M0 ()

import CaTTExp.Strict.OmegaSound ∅ closed as S
import CaTTExp.Strict.OmegaEval
module O = CaTTExp.Strict.OmegaEval ∅ Endo (λ k c → M0 k ≡ c)
open import CaTTExp.Strict.OmegaPasting Endo using (cp; cnil; ccons)

private
  isM : S.IsModel Endo M0
  isM ()

  mdet : O.Mk-det
  mdet {()}

  t f : Bool
  t = true
  f = false

  ρ : O.Env
  ρ = O.[]ₑ O.,ₑ X O.,ₑ Y O.,ₑ F [] O.,ₑ F (t ∷ []) O.,ₑ F (f ∷ [])

  vρ : O.ValidEnv ρ Γgh
  vρ 0 A refl = X , refl , refl , tt
  vρ 1 A refl = Y , refl , refl , tt
  vρ 2 A refl = F [] , refl , refl , O.ev-var refl , O.ev-var refl
  vρ 3 A refl = F (t ∷ []) , refl , refl , O.ev-var refl , O.ev-var refl
  vρ 4 A refl = F (f ∷ []) , refl , refl , O.ev-var refl , O.ev-var refl
  vρ (suc (suc (suc (suc (suc i))))) A ()

  -- vc a b denotes the vertical composite of the denotations.
  ev-vc : ∀ {a b u v} → O.Ev ρ a (F u) → O.Ev ρ b (F v) → O.Ev ρ (vc a b) (F (u ++ (v ++ [])))
  ev-vc {u = u} {v} ea eb =
    O.ev-coh
      (O.evs-cons (O.evs-cons (O.evs-cons (O.evs-cons (O.evs-cons (O.evs-cons (O.evs-cons O.evs-nil
        (O.ev-var refl)) (O.ev-var refl)) (O.ev-var refl)) (O.ev-var refl)) ea) (O.ev-var refl)) eb)
      (cp (ccons (cp (ccons (cp (cnil refl)) refl
                         (ccons (cp (cnil refl)) refl (cnil refl) refl) refl))
                 refl (cnil refl) refl))

  ev-gh : O.Ev ρ gh (F (t ∷ f ∷ []))
  ev-gh = ev-vc (O.ev-var refl) (O.ev-var refl)

  ev-hg : O.Ev ρ hg (F (f ∷ t ∷ []))
  ev-hg = ev-vc (O.ev-var refl) (O.ev-var refl)

  tf≢ft : F (t ∷ f ∷ []) ≡ F (f ∷ t ∷ []) → ⊥
  tf≢ft ()

-- No CaTT 3-cell g ∗₁ h ⇒ h ∗₁ g.
no-3cell : ∀ {w} → Γgh ⊢tm w ∶ arr ffTy gh hg → ⊥
no-3cell dw with S.sound-in Endo M0 isM dw vρ
... | c , _ , _ , e₁ , e₂ =
  tf≢ft (trans (sym (O.ev-det mdet e₁ ev-gh))
          (trans (sr2 0 c) (trans (sym (tg2 0 c)) (O.ev-det mdet e₂ ev-hg))))

------------------------------------------------------------------------
-- Yet the strict images (towers of bags) of g ∗₁ h and h ∗₁ g agree.

open import CaTTExp.Strict.Bag using (++-comm)
open import CaTTExp.Strict.Cell using (_≈w_; ≈w-refl)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (⟦_⟧; η)

gh≈hg : ⟦ gh ⟧ (η Γgh) ≈w ⟦ hg ⟧ (η Γgh)
gh≈hg = ≈w-refl _ , ≈w-refl _ , ++-comm ((4 ∷ []) ∷ []) ((3 ∷ []) ∷ [])
