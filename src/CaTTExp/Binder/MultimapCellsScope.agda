------------------------------------------------------------------------
-- The kernel images of the cell heads are scoped and locally closed
-- (ledger S26j, step 2b).
--
-- trTy k Φ C mentions no bound variable (`lc-trTy`), and, if C is
-- admitted and well formed in a context whose dependencies go down and
-- its entries are below j, only the variables below k + j: the k atoms
-- and the entries below j (`Sc.sc-trTy`). For a boundary that is not a
-- variable this is the support of the boundary, which stays below j
-- because the dependencies go down.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsScope where

open import CaTTExp.Prelude
open import CaTTExp.Binder.Multimap using (MMI; mmi; atomFm)
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.GrayForm using (GBF)
import CaTTExp.Binder.Syntax as Syntax
import CaTTExp.Binder.SyntaxLemmas as SL
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
open import CaTTExp.Gray.Biclosed.Strengthen using (Below; ∨-l; ∨-r; elem-++l; elem-++r)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_; Deps↓; Closed; cl-least; elem-split)
open import CaTTExp.Binder.MultimapCellsStrengthen using (inl; inr; upTo-elem)
open import CaTTExp.Binder.MultimapCellsRen using (filter-In-inv; upTo-In-inv; In-map-inv)

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt
  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p

  <-+l : ∀ k i j → T (i <ℕ j) → T (k + i <ℕ k + j)
  <-+l zero    i j p = p
  <-+l (suc k) i j p = <-+l k i j p

  below-l : ∀ j xs ys → Below j (xs ++ ys) → Below j xs
  below-l j xs ys h i p = h i (elem-++l i xs ys p)
  below-r : ∀ j xs ys → Below j (xs ++ ys) → Below j ys
  below-r j xs ys h i p = h i (elem-++r i xs ys p)

  self : ∀ n → T (n <ℕ suc n)
  self zero    = tt
  self (suc n) = self n

module _ (K B : Set) (injG : GBF → B) (injC : MMI → B) where

  open Syntax K B
  open SL K B using (T∧; ∧T; <-+; <-trans)
  open CellsConstruction K B injG injC

  ----------------------------------------------------------------------
  -- Substitutions of variables.

  sc-varsOf : ∀ n ρ js → T (scSub? n ρ) → (∀ j → In js j → T (j <ℕ n)) → T (scSub? n (varsOf ρ js))
  sc-varsOf n ρ []       p h = p
  sc-varsOf n ρ (j ∷ js) p h =
    sc-varsOf n (ρ ,ₛ var j) js (∧T p (h j (∨-l (j ==ℕ j) _ (==ℕ-refl j)))) (λ i q → h i (∨-r (i ==ℕ j) _ q))

  lc-varsOf : ∀ ρ js → T (lcSub? 0 ρ) → T (lcSub? 0 (varsOf ρ js))
  lc-varsOf ρ []       p = p
  lc-varsOf ρ (j ∷ js) p = lc-varsOf (ρ ,ₛ var j) js (∧T p tt)

  ----------------------------------------------------------------------
  -- Formulas.

  lc-fmV : ∀ x → T (lcTm? 0 (fmV x))
  lc-fmV (GB.obj _)  = tt
  lc-fmV (GB.rep _)  = tt
  lc-fmV (GB.shp _)  = tt
  lc-fmV (x GB.⊗ y)  = ∧T (lc-fmV x) (lc-fmV y)
  lc-fmV (x GB.\\ y) = ∧T (lc-fmV x) (lc-fmV y)
  lc-fmV (x GB.// y) = ∧T (lc-fmV x) (lc-fmV y)

  sc-fmV : ∀ k n x → (∀ i → T (i <ℕ k) → T (i <ℕ n)) → T (atomFm k x) → T (scTm? n (fmV x))
  sc-fmV k n (GB.obj i)  lt p = lt i p
  sc-fmV k n (GB.rep _)  lt ()
  sc-fmV k n (GB.shp _)  lt ()
  sc-fmV k n (x GB.⊗ y)  lt p = ∧T (sc-fmV k n x lt (∧-l _ _ p)) (sc-fmV k n y lt (∧-r _ _ p))
  sc-fmV k n (x GB.\\ y) lt p = ∧T (sc-fmV k n x lt (∧-l _ _ p)) (sc-fmV k n y lt (∧-r _ _ p))
  sc-fmV k n (x GB.// y) lt p = ∧T (sc-fmV k n x lt (∧-l _ _ p)) (sc-fmV k n y lt (∧-r _ _ p))

  ----------------------------------------------------------------------
  -- trTm is a variable or a head.

  trTm-elim : ∀ (P : Tm → Set) k Φ s → (∀ j → s ≡ GB.var j → P (var (k + j))) →
              ((∀ j → s ≡ GB.var j → ⊥) → P (trHead k Φ s)) → P (trTm k Φ s)
  trTm-elim P k Φ (GB.var j)       hv hh = hv j refl
  trTm-elim P k Φ (GB.mP _ _)      hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.eL _ _)      hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.eR _ _)      hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.pP _ _)      hv hh = hh (λ _ ())
  trTm-elim P k Φ GB.pt            hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.iP _)        hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.idt _)       hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.comp _ _)    hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.glue _ _ _)  hv hh = hh (λ _ ())
  trTm-elim P k Φ (GB.here _ _ _ _) hv hh = hh (λ _ ())

  ----------------------------------------------------------------------
  -- Local closure.

  lc-trHead : ∀ k Φ u → T (lcTm? 0 (trHead k Φ u))
  lc-trHead k Φ u =
    lc-varsOf (varsOf ⟨⟩ (catoms (canon k Φ u))) (GT.map (k +_) (cvars (canon k Φ u)))
      (lc-varsOf ⟨⟩ (catoms (canon k Φ u)) tt)

  lc-trTm : ∀ k Φ s → T (lcTm? 0 (trTm k Φ s))
  lc-trTm k Φ s = trTm-elim (λ t → T (lcTm? 0 t)) k Φ s (λ _ _ → tt) (λ _ → lc-trHead k Φ s)

  lc-trTy : ∀ k Φ C → T (lcTy? 0 (trTy k Φ C))
  lc-trTy k Φ (GB.op ((x ∷ []) GB.▸ z))     = ∧T (lc-fmV x) (lc-fmV z)
  lc-trTy k Φ (GB.op ([] GB.▸ _))           = tt
  lc-trTy k Φ (GB.op ((_ ∷ _ ∷ _) GB.▸ _))  = tt
  lc-trTy k Φ (GB.hom _ _ A s t)            = ∧T (lc-trTy k Φ A) (∧T (lc-trTm k Φ s) (lc-trTm k Φ t))

  ----------------------------------------------------------------------
  -- Scoping, below k atoms and j entries.

  module Sc (k : Nat) (Φ : GB.Ctx) (dd : Deps↓ Φ) (j : Nat) where

    n : Nat
    n = k + j

    atom-lt : ∀ i → T (i <ℕ k) → T (i <ℕ n)
    atom-lt i p = <-+ i k j p

    upTo-closed : Closed Φ (upTo j)
    upTo-closed v e vin i q = upTo-elem j i (<-trans i v j (dd v e i q) (upTo-In-inv j v vin))

    -- The support of a term below j is below j.
    sup-below : ∀ s {S} → GT.infer Φ s ≡ just S → Below j (varsT s) → Below j (varsY S) →
                ∀ v → In (supVars Φ s) v → T (v <ℕ j)
    sup-below s {S} eS bT bY v p =
      let (a , b) = filter-In-inv (λ i → elem i (closeFrom Φ (GT.length Φ) (supStart Φ s))) (upTo (GT.length Φ)) v p
      in upTo-In-inv j v (cl-least Φ (upTo j) upTo-closed (GT.length Φ) (supStart Φ s) (self (GT.length Φ)) h v a
                           (upTo-In-inv (GT.length Φ) v b))
      where
      h : ∀ i → In (supStart Φ s) i → T (i <ℕ GT.length Φ) → In (upTo j) i
      h i q _ with elem-split i (varsT s) (varsYM (GT.infer Φ s)) q
      ... | inl r = upTo-elem j i (bT i r)
      ... | inr r = upTo-elem j i (bY i (subst (λ m → In (varsYM m) i) eS r))

    sc-trHead : ∀ s {S} → GT.infer Φ s ≡ just S → Below j (varsT s) → Below j (varsY S) →
                T (scTm? n (trHead k Φ s))
    sc-trHead s eS bT bY =
      sc-varsOf n (varsOf ⟨⟩ (supAtoms k Φ s)) (GT.map (k +_) (supVars Φ s))
        (sc-varsOf n ⟨⟩ (supAtoms k Φ s) tt
          (λ i p → atom-lt i (upTo-In-inv k i (snd (filter-In-inv (λ i → elem i (supAtomsOf Φ s)) (upTo k) i p)))))
        (λ x p → let (v , vin , e) = In-map-inv (k +_) (supVars Φ s) x p in
                 subst (λ z → T (z <ℕ n)) (sym e) (<-+l k v j (sup-below s eS bT bY v vin)))

    sc-trTm : ∀ s {S} → GT.infer Φ s ≡ just S → Below j (varsT s) → Below j (varsY S) →
              T (scTm? n (trTm k Φ s))
    sc-trTm s eS bT bY =
      trTm-elim (λ t → T (scTm? n t)) k Φ s
        (λ v e → <-+l k v j (bT v (subst (λ u → In (varsT u) v) (sym e) (∨-l (v ==ℕ v) _ (==ℕ-refl v)))))
        (λ _ → sc-trHead s eS bT bY)

    eqMaybe-sound : ∀ m B → T (GT.eqMaybeTy m B) → m ≡ just B
    eqMaybe-sound (just A) B p = cong just (GB.eqTy-sound A B p)

    sc-trTy : ∀ C → T (okTy k C) → T (GT.wf Φ C) → Below j (varsY C) → T (scTy? n (trTy k Φ C))
    sc-trTy (GB.op ((x ∷ []) GB.▸ z)) p _ _ =
      ∧T (sc-fmV k n x atom-lt (∧-l _ _ p)) (sc-fmV k n z atom-lt (∧-r _ _ p))
    sc-trTy (GB.op ([] GB.▸ _)) () _ _
    sc-trTy (GB.op ((_ ∷ _ ∷ _) GB.▸ _)) () _ _
    sc-trTy (GB.hom d g A s t) p wC bC =
      let wA  = ∧-l _ _ wC
          wst = ∧-r (GT.wf Φ A) _ wC
          eS  = eqMaybe-sound (GT.infer Φ s) A (∧-l _ _ wst)
          eT  = eqMaybe-sound (GT.infer Φ t) A (∧-r (GT.eqMaybeTy (GT.infer Φ s) A) _ wst)
          bA  = below-l j (varsY A) (varsT s ++ varsT t) bC
          bst = below-r j (varsY A) (varsT s ++ varsT t) bC
      in ∧T (sc-trTy A (∧-r (g ==ℕ 1) _ p) wA bA)
            (∧T (sc-trTm s eS (below-l j (varsT s) (varsT t) bst) bA)
                (sc-trTm t eT (below-r j (varsT s) (varsT t) bst) bA))
