------------------------------------------------------------------------
-- No term at all has the type of the reverse interchanger.
--
-- Over ΣD¹ ∨ ΣD¹ (α : f ⇒ f′ : x → y, β : g ⇒ g′ : y → z), two-tier L
-- derives the interchanger (f◁β);(α▷g′) ⇛ (α▷g);(f′◁β)
-- (CaTTExp.Gray.Examples.ich-wf), and the reverse coh has no derivation
-- (no-ich⁻). This module proves the stronger statement of
-- notes/pseudo-vs-gray.md Theorem 1(2): no term t whatsoever, coh,
-- composite or otherwise, satisfies
--
--     HComp ⊢tm t ∶ (α▷g);(f′◁β) ⇛ (f◁β);(α▷g′).
--
-- Proof. By soundness (CaTTExp.Strict.Soundness), such a t would be a
-- 2-cell of ν(K(HComp)) from 0 to 5, so its top chain c would consist of
-- degree-2 basis elements, i.e. copies of α⊗β, and satisfy
--     ∂⁺c + (α▷g);(f′◁β) = ∂⁻c + (f◁β);(α▷g′).
-- Count the basis element f′⊗β: ∂⁺(α⊗β) = f′⊗β + α⊗g, ∂⁻(α⊗β) = f⊗β +
-- α⊗g′, so the left side has |c| + 1 copies and the right side none.
--
-- The result depends on the same two explicit module parameters as
-- soundness (T-cell and B-supp); nothing is postulated.
------------------------------------------------------------------------
module CaTTExp.Strict.ReverseInterchanger where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Soundness
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Examples using (HComp; ichTy⁻; αβ; βα)

private
  -- HComp's variables: x0 y1 f2 f'3 α4 z5 g6 g'7 β8.
  hcomp-ps : HComp ⊢ps
  hcomp-ps = snd (psOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ [])))

  -- Composable tuples from the object 5 to itself: only the unit.
  from5 : ∀ r → WFT HComp 5 5 r → r ≡ []
  from5 []      _ = refl
  from5 (0 ∷ r) (_ , () , _)
  from5 (1 ∷ r) (_ , () , _)
  from5 (2 ∷ r) (_ , () , _)
  from5 (3 ∷ r) (_ , () , _)
  from5 (4 ∷ r) (_ , () , _)
  from5 (5 ∷ r) (_ , () , _)
  from5 (6 ∷ r) (_ , () , _)
  from5 (7 ∷ r) (_ , () , _)
  from5 (8 ∷ r) (_ , () , _)
  from5 (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) ∷ r) (_ , () , _)

  -- Composable tuples from 1 to 5: one cell of the second hom.
  data From1 : Tuple → Set where
    g  : From1 (6 ∷ [])
    g' : From1 (7 ∷ [])
    β  : From1 (8 ∷ [])

  from1 : ∀ r → WFT HComp 1 5 r → From1 r
  from1 []      ()
  from1 (0 ∷ r) (_ , () , _)
  from1 (1 ∷ r) (_ , () , _)
  from1 (2 ∷ r) (_ , () , _)
  from1 (3 ∷ r) (_ , () , _)
  from1 (4 ∷ r) (_ , () , _)
  from1 (5 ∷ r) (_ , () , _)
  from1 (6 ∷ r) (_ , refl , p) rewrite from5 r p = g
  from1 (7 ∷ r) (_ , refl , p) rewrite from5 r p = g'
  from1 (8 ∷ r) (_ , refl , p) rewrite from5 r p = β
  from1 (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) ∷ r) (_ , () , _)

  zero≢suc : ∀ {n} → 0 ≡ suc n → ⊥
  zero≢suc ()

  one≢two : 1 ≡ 2 → ⊥
  one≢two ()

  -- The only basis element of degree 2 from 0 to 5 is α⊗β.
  basis2 : ∀ w → Basis HComp 0 5 2 w → w ≡ 4 ∷ 8 ∷ []
  basis2 []      (() , _)
  basis2 (0 ∷ r) ((_ , () , _) , _)
  basis2 (1 ∷ r) ((_ , () , _) , _)
  basis2 (2 ∷ r) ((_ , refl , p) , d) with from1 r p
  ... | g  = ⊥-elim (zero≢suc d)
  ... | g' = ⊥-elim (zero≢suc d)
  ... | β  = ⊥-elim (one≢two d)
  basis2 (3 ∷ r) ((_ , refl , p) , d) with from1 r p
  ... | g  = ⊥-elim (zero≢suc d)
  ... | g' = ⊥-elim (zero≢suc d)
  ... | β  = ⊥-elim (one≢two d)
  basis2 (4 ∷ r) ((_ , refl , p) , d) with from1 r p
  ... | g  = ⊥-elim (one≢two d)
  ... | g' = ⊥-elim (one≢two d)
  ... | β  = refl
  basis2 (5 ∷ r) ((_ , () , _) , _)
  basis2 (6 ∷ r) ((_ , () , _) , _)
  basis2 (7 ∷ r) ((_ , () , _) , _)
  basis2 (8 ∷ r) ((_ , () , _) , _)
  basis2 (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) ∷ r) ((_ , () , _) , _)

  -- The witness f′⊗β.
  a : Tuple
  a = 3 ∷ 8 ∷ []

  -- f′⊗β does not occur in ∂⁻ of any 2-chain from 0 to 5.
  count-∂⁻ : ∀ c → All (Basis HComp 0 5 2) c → count a (∂B HComp false c) ≡ 0
  count-∂⁻ []      _        = refl
  count-∂⁻ (w ∷ c) (b , bs) rewrite basis2 w b = count-∂⁻ c bs

  -- It occurs once in (α▷g);(f′◁β) and not in (f◁β);(α▷g′).
  count-αβ : count a (topS αβ) ≡ 1
  count-αβ = refl

  count-βα : count a (topS βα) ≡ 0
  count-βα = refl

  n+1≢0 : ∀ n → n + 1 ≡ 0 → ⊥
  n+1≢0 zero    ()
  n+1≢0 (suc n) ()

module _ (T-cell : TCell) (B-supp : BSupp) where

  open Soundness T-cell B-supp

  -- Theorem 1(2): no term has the reverse interchanger's type.
  no-reverse-interchanger : ∀ t → ¬ (HComp ⊢tm t ∶ ichTy⁻)
  no-reverse-interchanger t d with sound-tm (psInv hcomp-ps) d
  ... | (_ , refl , _ , _ , (_ , _ , _ , ch , bas)) =
    n+1≢0 (count a (∂B HComp true c))
      (trans (sym (trans (count-++ a (∂B HComp true c) (topS αβ))
                         (cong (count a (∂B HComp true c) +_) count-αβ)))
      (trans (at ch a)
      (trans (count-++ a (∂B HComp false c) (topS βα))
             (cong₂ _+_ (count-∂⁻ c bas) count-βα))))
    where c = topS t
