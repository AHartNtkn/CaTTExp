------------------------------------------------------------------------
-- Radicality and (F2) for cells of K(Γ)(x, y), Γ a pasting context
-- (notes/conjectures/answered/steiner-support-formalizable-2026-11-18.md,
-- §3), without atoms.
--
--   R q : every coefficient of the top chain of a q-cell is ≤ 1;
--   H q : for a (q+1)-cell step S U c, every coefficient of
--         top S + ∂⁺c is ≤ 1.
--
-- R 0 is augmentation; R q ⇒ H q applies R q to the cut at a
-- (Strict.Cut.cut-cell, cut-at); H q ⇒ R (q+1) uses a positive face of
-- each basis element of positive degree. (F2) follows from H.
------------------------------------------------------------------------
module CaTTExp.Strict.Rad where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Cut
open import CaTTExp.Strict.TopCell using (Pos)
open import CaTTExp.Strict.CohCase using (count-∈L; All-∈L; ∈L-++r)
open import CaTTExp.Strict.Order using (OInv; oinv-⊢ps)
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (Any; _≤_; z≤n; s≤s; ≤-trans; ≤-refl; n≤m+n; m≤m+n)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_)

------------------------------------------------------------------------
-- Counting and membership.

∈L-count : ∀ a X → a ∈L X → Pos (count a X)
∈L-count a (x ∷ X) (hereA refl) rewrite eqT-refl a = tt
∈L-count a (x ∷ X) (thereA m) with eqT a x
... | true  = tt
... | false = ∈L-count a X m

pos-≤ : ∀ {m n} → Pos m → m ≤ n → Pos n
pos-≤ {suc m} {suc n} _ _ = tt

private
  plus-ge : ∀ m k l → Pos m → k ≤ l → suc k ≤ m + l
  plus-ge (suc m) k l _ le = s≤s (≤-trans le (n≤m+n m l))

cm-ge : ∀ g c a p → Pos (count p (g a)) → count a c ≤ count p (cm g c)
cm-ge g []      a p h = z≤n
cm-ge g (x ∷ c) a p h with eqT a x in e
... | true rewrite eqT-sound a x (subst T (sym e) tt) =
  subst (suc (count x c) ≤_) (sym (count-++ p (g x) (cm g c))) (plus-ge _ _ _ h (cm-ge g c x p h))
... | false =
  subst (count a c ≤_) (sym (count-++ p (g x) (cm g c))) (≤-trans (cm-ge g c a p h) (n≤m+n _ _))

cm-mem : ∀ g c p → Pos (count p (cm g c)) → Σ Tuple λ b → (b ∈L c) × Pos (count p (g b))
cm-mem g []      p ()
cm-mem g (x ∷ c) p h with count p (g x) in e
... | suc _ = x , hereA refl , subst Pos (sym e) tt
... | zero with cm-mem g c p (subst Pos (trans (count-++ p (g x) (cm g c)) (cong (_+ count p (cm g c)) e)) h)
...   | b , m , q = b , thereA m , q

consB-mem⇐ : ∀ v Y {z} → z ∈L Y → (v ∷ z) ∈L consB v Y
consB-mem⇐ v (y ∷ Y) (hereA refl) = hereA refl
consB-mem⇐ v (y ∷ Y) (thereA m)   = thereA (consB-mem⇐ v Y m)

setTop-top : ∀ S w → top (setTop S w) ≡ w
setTop-top (base _)     w = refl
setTop-top (step _ _ _) w = refl

------------------------------------------------------------------------
-- Every basis element of positive degree has faces of both signs.

module _ {Γ : Ctx} (inv : PsInv Γ) where

  face-exists : ∀ σ w k → deg Γ w ≡ suc k → Σ Tuple λ z → z ∈L ∂T Γ σ w
  face-exists σ []      k ()
  face-exists σ (v ∷ w) k d with vshape' inv v
  ... | flatS' h0 with face-exists (flipN (hdimV Γ v) σ) w k (trans (cong (_+ deg Γ w) (sym h0)) d)
  ...   | z , m = v ∷ z , ∈L-++r (here σ (facesTy (lookup Γ v)) w) (consB-mem⇐ v _ m)
  face-exists σ (v ∷ w) k d | deep' s t ef =
    (if σ then t else s) ∷ w ,
    subst (λ F → ((if σ then t else s) ∷ w) ∈L (here σ F w ++ consB v (∂T Γ (flipN (hdimV Γ v) σ) w))) (sym ef) (hereA refl)

------------------------------------------------------------------------
-- The induction.

module _ {Γ : Ctx} (P : Γ ⊢ps) {x y : Nat} where
  private
    I   = oinv-⊢ps P
    inv = psInv P
    topBas = Cells.IsCell-top (∂T Γ) (Basis Γ x y)

  R : Nat → Set
  R q = ∀ X → IsCellL Γ x y q X → ∀ a → count a (top X) ≤ 1

  H : Nat → Set
  H q = ∀ S U c → IsCellL Γ x y (suc q) (step S U c) → ∀ a → count a (top S) + count a (∂B Γ true c) ≤ 1

  private
    one-le : ∀ a w → count a (w ∷ []) ≤ 1
    one-le a w with eqT a w
    ... | true  = s≤s z≤n
    ... | false = z≤n

    r0 : R 0
    r0 (base c) (w , p , _) a = subst (_≤ 1) (sym (at p a)) (one-le a w)

    r→h : ∀ q → R q → H q
    r→h q r S U c (cS , cU , par , ch , ac) a =
      subst (_≤ 1) (cut-at I a (top S) (top U) c)
        (subst (λ w → count a w ≤ 1) (setTop-top S _)
          (r _ (cut-cell I inv q a S (top U) c cS (topBas q U cU) ac ch) a))

    h→r : ∀ q → H q → R (suc q)
    h→r q h (step S U c) cell@(cS , cU , par , ch , ac) a with count a c in e
    ... | zero  = z≤n
    ... | suc m with face-exists inv true a q (snd (All-∈L c ac (count-∈L a c (subst Pos (sym e) tt))))
    ...   | p , mp =
      subst (_≤ 1) e (≤-trans (cm-ge (∂T Γ true) c a p (∈L-count p _ mp))
                     (≤-trans (n≤m+n (count p (top S)) _) (h S U c cell p)))

  rad : ∀ q → R q
  rad zero    = r0
  rad (suc q) = h→r q (r→h q (rad q))

  hbound : ∀ q → H q
  hbound q = r→h q (rad q)

  -- The other side: top U + ∂⁻c ≤ 1.
  hbound⁻ : ∀ q S U c → IsCellL Γ x y (suc q) (step S U c) →
            ∀ a → count a (top U) + count a (∂B Γ false c) ≤ 1
  hbound⁻ q S U c cell@(_ , _ , _ , ch , _) a =
    subst (_≤ 1) (trans (+-comm (count a (top S)) _)
                 (trans (sym (count-++ a (∂B Γ true c) (top S)))
                 (trans (at ch a)
                 (trans (count-++ a (∂B Γ false c) (top U)) (+-comm _ (count a (top U)))))))
          (hbound q S U c cell a)

  private
    zero-of : ∀ s p → s + p ≤ 1 → Pos p → s ≡ 0
    zero-of zero    p       _           _ = refl
    zero-of (suc s) (suc p) (s≤s le) _ = ⊥-elim (no (subst (_≤ 0) (+-suc s p) le))
      where
      no : ∀ {n} → suc n ≤ 0 → ⊥
      no ()

  -- (F2): positive faces of the top chain avoid the source row,
  -- negative faces avoid the target row.
  f2⁺ : ∀ q S U c → IsCellL Γ x y (suc q) (step S U c) → ∀ b a → b ∈L c → a ∈L ∂T Γ true b →
        count a (top S) ≡ 0
  f2⁺ q S U c cell b a mb ma =
    zero-of _ _ (hbound q S U c cell a) (pos-≤ (∈L-count b c mb) (cm-ge (∂T Γ true) c b a (∈L-count a _ ma)))

  f2⁻ : ∀ q S U c → IsCellL Γ x y (suc q) (step S U c) → ∀ b a → b ∈L c → a ∈L ∂T Γ false b →
        count a (top U) ≡ 0
  f2⁻ q S U c cell b a mb ma =
    zero-of _ _ (hbound⁻ q S U c cell a) (pos-≤ (∈L-count b c mb) (cm-ge (∂T Γ false) c b a (∈L-count a _ ma)))
