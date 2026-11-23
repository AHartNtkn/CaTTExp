------------------------------------------------------------------------
-- The sort check of the mm and mmc heads (ledger S26j).
--
--  * dataInst-dsub: a here node passes `dataInst k` exactly when its
--    instance substitution is data-sorted in the sense of
--    `Gray.Biclosed.SortDisc` (DSub from the template's data variable
--    to the atoms below k), so a sorted term that infers uses only
--    kernel instances (KInst), with every atom data-sorted;
--  * sortedT-ren, sortedY-ren: renaming atoms into range and entries
--    onto a support keeps a term or type sorted (used for canonical
--    heads, `MultimapCellsWf`).
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapSorted where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Templates using (_∈_; here!; there!)
open import CaTTExp.Gray.Biclosed.SortDisc using (nonRep; headVar; tmplData; DSub; fromMaybe)
open import CaTTExp.Binder.Multimap using (headBelow; dataFm; dataInst; sortedT; sortedTs; sortedY)
open import CaTTExp.Binder.MultimapCells using (atF; atFs; atT; atTs; atY; renOf; idx; upTo)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_)
open import CaTTExp.Binder.MultimapCellsRen using (⊆-l; ⊆-r; idx-lt)
open import CaTTExp.Binder.MultimapCellsStrengthen using (upTo-elem)
open import CaTTExp.Gray.Biclosed.Strengthen using (∨-l; ∨-r; elem-++l; elem-++r)

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true b _ = tt
  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true b p = p
  ∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in {true} _ q = q

------------------------------------------------------------------------
-- dataInst is SortDisc's data-sorted condition.

elem→∈′ : ∀ i xs → T (elem i xs) → i ∈ xs
elem→∈′ i (x ∷ xs) p with i ==ℕ x in e
... | true  rewrite ==ℕ-sound i x (subst T (sym e) tt) = here!
... | false = there! (elem→∈′ i xs p)

∈→elem : ∀ {i} xs → i ∈ xs → T (elem i xs)
∈→elem (x ∷ xs) here!      = ∨-l (x ==ℕ x) _ (==ℕ-refl x)
∈→elem (x ∷ xs) (there! p) = ∨-r _ _ (∈→elem xs p)

all-∈ : ∀ (P : Nat → Bool) xs → T (all P xs) → ∀ i → i ∈ xs → T (P i)
all-∈ P (x ∷ xs) a i here!      = ∧-l _ _ a
all-∈ P (x ∷ xs) a i (there! p) = all-∈ P xs (∧-r (P x) _ a) i p

upTo-∈ : ∀ k j → T (j <ℕ k) → j ∈ upTo k
upTo-∈ k j l = elem→∈′ j (upTo k) (upTo-elem k j l)

-- A sorted here node's instance is data-sorted, with the atoms below k
-- as the data-sorted variables.
dataInst-dsub : ∀ k t φs ts → T (dataInst k t φs) → DSub (tmplData t) (upTo k) (instS φs ts)
dataInst-dsub k t φs ts d i i∈ =
  let p = all-∈ (dataFm k φs) (tmplData t) d i i∈
      q = ∧-r (i <ℕ length φs) _ p
  in ∧-l _ _ q , λ j e → upTo-∈ k j (hb (headVar (nthF φs i)) e (∧-r (nonRep (nthF φs i)) _ q))
  where
  hb : ∀ {j} m → m ≡ just j → T (headBelow k m) → T (j <ℕ k)
  hb (just j) refl p = p

------------------------------------------------------------------------
-- Renaming keeps sortedness.

all-mono : ∀ (P Q : Nat → Bool) xs → (∀ i → T (P i) → T (Q i)) → T (all P xs) → T (all Q xs)
all-mono P Q []       h a = tt
all-mono P Q (x ∷ xs) h a = ∧-in (h x (∧-l _ _ a)) (all-mono P Q xs h (∧-r (P x) _ a))

length-sFs : ∀ φ xs → length (sFs φ xs) ≡ length xs
length-sFs φ []       = refl
length-sFs φ (x ∷ xs) = cong suc (length-sFs φ xs)

nthF-sFs′ : ∀ φ xs i → T (i <ℕ length xs) → nthF (sFs φ xs) i ≡ sF φ (nthF xs i)
nthF-sFs′ φ (x ∷ xs) zero    _ = refl
nthF-sFs′ φ (x ∷ xs) (suc i) l = nthF-sFs′ φ xs i l

atF-nth : ∀ xs i → T (i <ℕ length xs) → atF (nthF xs i) ⊆ atFs xs
atF-nth (x ∷ xs) zero    _ j p = elem-++l j (atF x) (atFs xs) p
atF-nth (x ∷ xs) (suc i) l j p = elem-++r j (atF x) (atFs xs) (atF-nth xs i l j p)

module Ren (as vs : List Nat) where
  private ρ = renOf as vs

  nonRep-ren : ∀ x → T (nonRep x) → T (nonRep (sF (fo ρ) x))
  nonRep-ren (obj _)  _ = tt
  nonRep-ren (rep _)  ()
  nonRep-ren (shp _)  _ = tt
  nonRep-ren (_ ⊗ _)  _ = tt
  nonRep-ren (_ \\ _) _ = tt
  nonRep-ren (_ // _) _ = tt

  head-ren : ∀ x → atF x ⊆ as → T (headBelow (length as) (headVar (sF (fo ρ) x)))
  head-ren (obj i)  h = idx-lt as i (h i (∨-l (i ==ℕ i) _ (==ℕ-refl i)))
  head-ren (rep _)  h = tt
  head-ren (shp _)  h = tt
  head-ren (_ ⊗ _)  h = tt
  head-ren (_ \\ _) h = tt
  head-ren (_ // _) h = tt

  dataFm-ren : ∀ k φs i → atFs φs ⊆ as → T (dataFm k φs i) → T (dataFm (length as) (sFs (fo ρ) φs) i)
  dataFm-ren k φs i h p =
    let l = ∧-l _ _ p
        q = ∧-r (i <ℕ length φs) _ p
        e = nthF-sFs′ (fo ρ) φs i l
    in ∧-in (subst (λ n → T (i <ℕ n)) (sym (length-sFs (fo ρ) φs)) l)
            (∧-in (subst (λ x → T (nonRep x)) (sym e) (nonRep-ren (nthF φs i) (∧-l _ _ q)))
                  (subst (λ x → T (headBelow (length as) (headVar x))) (sym e)
                     (head-ren (nthF φs i) (λ j r → h j (atF-nth φs i l j r)))))

  mutual
    sortedT-ren : ∀ k u → atT u ⊆ as → T (sortedT k u) → T (sortedT (length as) (sT ρ u))
    sortedT-ren k (var x)      h p = var-case (elem x vs)
      where
      var-case : ∀ b → T (sortedT (length as) (if b then var (idx x vs) else pt))
      var-case true  = tt
      var-case false = tt
    sortedT-ren k (mP _ _)     h p = tt
    sortedT-ren k (eL _ _)     h p = tt
    sortedT-ren k (eR _ _)     h p = tt
    sortedT-ren k (pP _ _)     h p = tt
    sortedT-ren k pt           h p = tt
    sortedT-ren k (iP _)       h p = tt
    sortedT-ren k (idt _)      h p = tt
    sortedT-ren k (comp f gs)  h p =
      ∧-in (sortedT-ren k f (⊆-l (atT f) (atTs gs) as h) (∧-l _ _ p))
           (sortedTs-ren k gs (⊆-r (atT f) (atTs gs) as h) (∧-r (sortedT k f) _ p))
    sortedT-ren k (glue a x b) h p =
      let h₂ = ⊆-r (atT a) (atT x ++ atT b) as h
          p₂ = ∧-r (sortedT k a) _ p
      in ∧-in (sortedT-ren k a (⊆-l (atT a) (atT x ++ atT b) as h) (∧-l _ _ p))
              (∧-in (sortedT-ren k x (⊆-l (atT x) (atT b) as h₂) (∧-l _ _ p₂))
                    (sortedT-ren k b (⊆-r (atT x) (atT b) as h₂) (∧-r (sortedT k x) _ p₂)))
    sortedT-ren k (here t e φs ts) h p =
      ∧-in (all-mono (dataFm k φs) (dataFm (length as) (sFs (fo ρ) φs)) (tmplData t)
              (λ i → dataFm-ren k φs i (⊆-l (atFs φs) (atTs ts) as h)) (∧-l _ _ p))
           (sortedTs-ren k ts (⊆-r (atFs φs) (atTs ts) as h) (∧-r (dataInst k t φs) _ p))

    sortedTs-ren : ∀ k us → atTs us ⊆ as → T (sortedTs k us) → T (sortedTs (length as) (sTs ρ us))
    sortedTs-ren k []       h p = tt
    sortedTs-ren k (u ∷ us) h p =
      ∧-in (sortedT-ren k u (⊆-l (atT u) (atTs us) as h) (∧-l _ _ p))
           (sortedTs-ren k us (⊆-r (atT u) (atTs us) as h) (∧-r (sortedT k u) _ p))

  sortedY-ren : ∀ k A → atY A ⊆ as → T (sortedY k A) → T (sortedY (length as) (sY ρ A))
  sortedY-ren k (op _)          h p = tt
  sortedY-ren k (hom m g A s t) h p =
    let h₂ = ⊆-r (atY A) (atT s ++ atT t) as h
        p₂ = ∧-r (sortedY k A) _ p
    in ∧-in (sortedY-ren k A (⊆-l (atY A) (atT s ++ atT t) as h) (∧-l _ _ p))
            (∧-in (sortedT-ren k s (⊆-l (atT s) (atT t) as h₂) (∧-l _ _ p₂))
                  (sortedT-ren k t (⊆-r (atT s) (atT t) as h₂) (∧-r (sortedT k s) _ p₂)))
