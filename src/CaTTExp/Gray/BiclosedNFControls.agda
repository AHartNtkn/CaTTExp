------------------------------------------------------------------------
-- Negative controls for the checks in BiclosedNF.
--
-- `disjoint` has two redex occurrences (η in the first curry, η in the
-- last), but they share no triple: N cannot fire at the middle
-- generator and the last curry, because the curry's left context x 8
-- does not extend the generator's empty context.  So `overlapping`
-- must say false while the reduct count is two.
--
-- `k 0` is well typed from x 5 and ill typed from x 6.
------------------------------------------------------------------------
module CaTTExp.Gray.BiclosedNFControls where

open import CaTTExp.Prelude
open import CaTTExp.Gray.BiclosedNF

x : Nat → Formula
x n = atom n ∷ []

kc : Nat → Formula → Triple
kc n c = tri c (cur Ld (x 1) (x 3) (x 5)
  (tri (x 1) (gen n (x 5) (lres (x 1) (x 3) ∷ [])) []
   ∷ tri [] (ev Ld (x 1) (x 3)) [] ∷ [])) []

k : Nat → Triple
k n = kc n []

disjoint : Word
disjoint = k 0 ∷ tri [] (gen 9 (lres (x 1) (x 3) ∷ []) (x 5)) [] ∷ kc 1 (x 8) ∷ []

atLeast2 : List Word → Bool
atLeast2 (_ ∷ _ ∷ _) = true
atLeast2 _           = false

disjoint-two-redexes : T (atLeast2 (reducts disjoint))
disjoint-two-redexes = tt

disjoint-no-overlap : T (not (overlapping disjoint))
disjoint-no-overlap = tt

k-typed : T (wellTyped (x 5) (k 0 ∷ []))
k-typed = tt

k-wrong-source : T (not (wellTyped (x 6) (k 0 ∷ [])))
k-wrong-source = tt
