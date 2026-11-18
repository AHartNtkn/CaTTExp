------------------------------------------------------------------------
-- Rows of composites in ν(K), and the rows of an expression with one
-- generator above r (ledger A5, step L3; outside response §3.2 (10)).
--
-- Above the composition level, rows of a composite add; above n, the
-- rows of an n-boundary vanish. Hence an expression with exactly one
-- generator ⟨a⟩ of degree > r has the rows of ⟨a⟩ above r
-- (`single-rows`).
------------------------------------------------------------------------
module CaTTExp.Strict.NuRows where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.Expr
open import CaTTExp.Strict.BdElim
open import CaTTExp.Strict.NuWords
open import CaTTExp.Strict.Bag using (+-zero)
import CaTTExp.Strict.Std as S
open import CaTTExp.Strict.StdSem using (module StdSem)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Tables, entry by entry.

module TabAt (𝕄 : CMon) where
  open CMon 𝕄

  private
    z = zP 𝕄
    _+p_ = _+P_ 𝕄

  zz : z +p z ≡ z
  zz = cong₂ _,_ (⊕-id ε) (⊕-id ε)

  at-zeros : ∀ {m} j → at z (zeros 𝕄 {m}) j ≡ z
  at-zeros {zero}  j       = refl
  at-zeros {suc m} zero    = refl
  at-zeros {suc m} (suc j) = at-zeros {m} j

  at-add : ∀ {m} (x y : Tab 𝕄 m) j → at z (add 𝕄 x y) j ≡ at z x j +p at z y j
  at-add []      []       j       = sym zz
  at-add (e ∷ r) (e′ ∷ r′) zero    = refl
  at-add (e ∷ r) (e′ ∷ r′) (suc j) = at-add r r′ j

  at-comp : ∀ {m} n (x y : Tab 𝕄 m) j → n < j → at z (compT 𝕄 n x y) j ≡ at z x j +p at z y j
  at-comp n       []            []            j       l       = sym zz
  at-comp zero    ((a , b) ∷ r) ((c , d) ∷ s) (suc j) l       = at-add r s j
  at-comp (suc n) (e ∷ r)       (e′ ∷ s)      (suc j) (s≤s l) = at-comp n r s j l

  at-src : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at z (srcT 𝕄 n x) j ≡ z
  at-src n       []            j       l       = refl
  at-src {suc m} zero ((a , b) ∷ r) (suc j) l   = at-zeros {m} j
  at-src (suc n) (e ∷ r)       (suc j) (s≤s l) = at-src n r j l

  at-tgt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at z (tgtT 𝕄 n x) j ≡ z
  at-tgt n       []            j       l       = refl
  at-tgt {suc m} zero ((a , b) ∷ r) (suc j) l   = at-zeros {m} j
  at-tgt (suc n) (e ∷ r)       (suc j) (s≤s l) = at-tgt n r j l

------------------------------------------------------------------------
-- Atoms and single-high expressions.

module Rows {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) where
  open Basis B
  open Hyp H
  open Atom B
  open Gen B H L
  open TabAt (ADC.𝕄 K)

  private
    module ν = ωCat (nu K L)

  rows : Cell K L → RF
  rows x = at 0R (fst x)

  -- Atoms have dimension deg.
  dim-atom : ∀ i (iN : i < N) (iL : deg i ≤ L) → ν.src (deg i) (atom i iN iL) ≡ atom i iN iL
  dim-atom i iN iL = ≡-cell K L
    (trans (cong (srcT (ADC.𝕄 K) (deg i)) (atomT≡ (ent i) 0))
      (trans (src-tab (deg i) 0 (ent i))
        (trans (tabE (srcF (deg i + 0) (ent i)) (ent i) 0 pt) (sym (atomT≡ (ent i) 0)))))
    where
    pt : ∀ j → 0 ≤ j → srcF (deg i + 0) (ent i) j ≡ ent i j
    pt j _ rewrite +-zero (deg i) with view3 j (deg i)
    ... | vlt l    rewrite cmp3-lt l = refl
    ... | veq refl rewrite cmp3-eq (deg i) =
      cong (fst (ent i (deg i)) ,_) (ent-last-at i)
      where
      ent-last-at : ∀ i → fst (ent i (deg i)) ≡ snd (ent i (deg i))
      ent-last-at i = Cells.Deg.ent-last dd deg-dp deg-dm (deg i) i 0 (sym (+-zero (deg i)))
    ... | vgt l    rewrite cmp3-gt l = sym (ent-zero i j l)

  private
    at-tabG : ∀ {m} (d : Row) (f : RF) k j → j < m → at d (tabG {m = m} f k) j ≡ f (j + k)
    at-tabG {suc m} d f k zero    _       = refl
    at-tabG {suc m} d f k (suc j) (s≤s l) = trans (at-tabG {m} d f (suc k) j l) (cong f (+-suc′ j k))
      where
      +-suc′ : ∀ j k → j + suc k ≡ suc (j + k)
      +-suc′ zero    k = refl
      +-suc′ (suc j) k = cong suc (+-suc′ j k)

  rows-atom : ∀ i (iN : i < N) (iL : deg i ≤ L) j → j ≤ L → rows (atom i iN iL) j ≡ ent i j
  rows-atom i iN iL j jL =
    trans (cong (λ t → at 0R t j) (atomT≡ {suc L} (ent i) 0))
      (trans (at-tabG {suc L} 0R (ent i) 0 j (s≤s jL)) (cong (ent i) (+-zero j)))

  rows-src : ∀ n x j → n < j → rows (ν.src n x) j ≡ 0R
  rows-src n (x , _) j l = at-src n x j l

  rows-comp : ∀ n x y p j → n < j → rows (ν.comp n x y p) j ≡ rows x j +R rows y j
  rows-comp n (x , _) (y , _) p j l = at-comp n x y j l

  -- Expressions with one generator above r have that atom's rows above r.
  module Single (W : Sd → AtomG B H L → Expr (AtomG B H L)) where
    degG : AtomG B H L → Nat
    degG (i , _ , _) = deg i

    open S.Std degG W
    open Syn degG W using (CO; co-gen; co-cmp)
    open Eval (nu K L) (ιν B H L)
    open StdSem (nu K L) (ιν B H L) using (absorb-l; absorb-r; Dim)

    dimν : ∀ g → ν.src (degG g) (ιν B H L g) ≡ ιν B H L g
    dimν (i , iN , iL) = dim-atom i iN iL

    open DimProof (nu K L) (ιν B H L) dimν

    private
      Dim-up : ∀ {r k y} → r ≤ k → Dim r y → Dim k y
      Dim-up {r} {k} {y} l d = trans (cong (ν.src k) (sym d)) (trans (ν.src-src-≥ y l) d)

      sum1 : ∀ {a b} → a + b ≡ 1 → ((a ≡ 0) × (b ≡ 1)) ⊎ ((a ≡ 1) × (b ≡ 0))
      sum1 {zero}        e  = inj₁ (refl , e)
      sum1 {suc zero} {zero} e = inj₂ (refl , refl)

    single-rows : ∀ r f {y} → CO f → hi r f ≡ 1 → Ev f y →
                  Σ (AtomG B H L) (λ g → (r < degG g) × (∀ j → r < j → j ≤ L → rows y j ≡ ent (fst g) j))
    single-rows r (gen (i , iN , iL)) (co-gen _) h (ev-gen _) with tri r (deg i)
    ... | tri< l = (i , iN , iL) , l , λ j _ jL → rows-atom i iN iL j jL
    single-rows r (gen g) (co-gen _) () (ev-gen _) | tri≡ _
    single-rows r (gen g) (co-gen _) () (ev-gen _) | tri> _
    single-rows r (cmp k a b) (co-cmp _ ca cb) h (ev-cmp .k {x = y} {y = z} u v p) with sum1 {hi r a} h
    ... | inj₁ (ha , hb) =
      let (g , l , rw) = single-rows r b cb hb v in
      g , l , λ j rj jL → trans (eq j rj) (rw j rj jL)
      where
      dy : Dim r y
      dy = dimLe (hi→DegLe ca ha) u
      eq : ∀ j → r < j → rows (ν.comp k y z p) j ≡ rows z j
      eq j rj with tri k r
      ... | tri< kr = trans (rows-comp k y z p j (≤-trans (s≤s (<→≤ kr)) rj))
                            (trans (cong (_+R rows z j) (trans (cong (λ t → rows t j) (sym dy)) (rows-src r y j rj)))
                                   (+R-idl (rows z j)))
      ... | tri≡ refl = cong (λ t → rows t j) (absorb-l dy p)
      ... | tri> rk = cong (λ t → rows t j) (absorb-l (Dim-up (<→≤ rk) dy) p)
    ... | inj₂ (ha , hb) =
      let (g , l , rw) = single-rows r a ca ha u in
      g , l , λ j rj jL → trans (eq j rj) (rw j rj jL)
      where
      dz : Dim r z
      dz = dimLe (hi→DegLe cb hb) v
      eq : ∀ j → r < j → rows (ν.comp k y z p) j ≡ rows y j
      eq j rj with tri k r
      ... | tri< kr = trans (rows-comp k y z p j (≤-trans (s≤s (<→≤ kr)) rj))
                            (trans (cong (rows y j +R_) (trans (cong (λ t → rows t j) (sym dz)) (rows-src r z j rj)))
                                   (+R-idr (rows y j)))
      ... | tri≡ refl = cong (λ t → rows t j) (absorb-r dz p)
      ... | tri> rk = cong (λ t → rows t j) (absorb-r (Dim-up (<→≤ rk) dz) p)
