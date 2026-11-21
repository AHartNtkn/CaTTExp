------------------------------------------------------------------------
-- Dualities and the uniform lax core V + S (ledger D8, uniform part).
--
-- Companion to notes/closed-structure.md, Part D, §D.4.  GrayDuality
-- treats two-tier L, where interchange is directed only along 0-cells.
-- In the uniform core (spec chapter 2, §2.3) interchange is directed at
-- every level.  At level n the Gray-type configuration is two
-- (n+2)-cells α (left) and β (right) juxtaposed along an n-cell, over
-- Σⁿ(ΣD¹ ∨ ΣD¹); its elementary interchanger is the (n+3)-cell
--     χ : (β's part first) ⇛ (α's part first)        ("right first")
-- between the two composites along (n+1)-cells, and no admissible theory
-- has its reverse (requirement 3).  An ambient duality D_J reverses the
-- cells whose dimension lies in J; as in GrayDuality, a sign J n = false
-- means n ∈ J.
--
-- Part 1 (the orientation computation).  For a configuration of
-- (l+1)-cells juxtaposed along a k-cell, D_J acts by three independent
-- flips, one per dimension that matters: k+1 (the k-composition
-- reverses, so left and right operands trade places), l+1 (the
-- l-composition reverses, so the other part comes first) and l+2 (the
-- cell itself is reversed).  dual-canonical: the dual of the canonical
-- orientation is canonical iff Row J k l = J(k+1) · J(l+1) · J(l+2) is
-- +1, and reversed iff it is −1.  The three flips are the definition of
-- the action (dualIch); what is checked is that their composite is
-- governed by that one sign.  The theorem below only uses l = k+1.
--
-- Part 2 (classification).
--   * kernel-theorem: the Gray rows (n, n+1) at every level together
--     with the two-tier test (the k = 0 rows, equivalently GrayDuality's
--     Symmetry / ToOplax) all equal c  iff  J n = c for every n ≥ 1.  So
--     the only symmetry of the uniform core is J = ∅, and the only
--     duality onto the oplax core is J = all.
--   * J124-gray-rows, J124-not-two-tier, op-two-tier, op-gray-rows:
--     neither half suffices alone.  J = {1,2,4,5,7,8,…} passes every
--     Gray row and fails the two-tier test; op (J = odd) passes the
--     two-tier test and reverses the Gray interchanger at level 1
--     (op-row-1-2, op-reverses-1-2: a 4-cell between composites of
--     3-cells juxtaposed along a 1-cell).
--   * level0↔Symmetry, level0↔ToOplax: the k = 0 rows (0, l), l ≥ 1,
--     are exactly the two-tier conditions.
--   * all-rows↔const, all-rows↔shifts and corollaries: if every pair
--     k < l is counted as a row (the picture of closed-structure.md §D.3,
--     where each level carries the full Gray orientation data), all rows
--     equal c iff every shift of J passes the two-tier test iff J is
--     constant c.  This agrees with kernel-theorem; it is arithmetic
--     about Row, and its rows with l > k+1 are not used by the theorem.
--
-- Part 3 (the switches).  The two visible laws of the settings are the
-- split of a composite left operand (the inner law) and of a composite
-- right operand (R) of an interchanger at some level k.  D_J trades left
-- and right operands at level k iff k+1 ∈ J, so it exchanges the two
-- splits there.  dual-has: the dual setting contains exactly the duals
-- of the laws of the original one.  total-mirror: the total duality
-- exchanges iccS and rspS and fixes vS and allS.  level-uniform: the
-- dual of a single setting is the same at every level iff the setting
-- is mirror-symmetric (vS or allS) or J (k+1) does not depend on k.
--
-- Not proved here, argued in the note (§D.4.1): that D_J acts on the
-- configuration by exactly these three flips (dualIch is that statement,
-- taken as a definition); that a reversed Gray row gives an accepted
-- coherence whose dual is rejected (requirement 3); and that the
-- two-tier test is necessary for uniform L (its witnesses live on
-- contexts ΣD¹ ∨ ΣDᵠ, where uniform and two-tier L agree).
------------------------------------------------------------------------
module CaTTExp.GrayDualityUniform where

open import CaTTExp.Prelude
open import CaTTExp.GrayDuality
open import CaTTExp.Join.SwitchLaws using (Switches; vS; iccS; rspS; allS)
open Switches

------------------------------------------------------------------------
-- Sign algebra used below.

·-unitʳ : ∀ a → a · true ≡ a
·-unitʳ true  = refl
·-unitʳ false = refl

·-sq : ∀ a → a · a ≡ true
·-sq true  = refl
·-sq false = refl

·-true : ∀ a b → a · b ≡ true → a ≡ b
·-true true  true  _ = refl
·-true true  false ()
·-true false true  ()
·-true false false _ = refl

·-cancelʳ : ∀ a b c → a · c ≡ b · c → a ≡ b
·-cancelʳ true  true  c _ = refl
·-cancelʳ false false c _ = refl
·-cancelʳ true  false true  ()
·-cancelʳ true  false false ()
·-cancelʳ false true  true  ()
·-cancelʳ false true  false ()

-- (a·b·c)·(a'·b'·c') = (a·a')·(b·b')·(c·c')
·-mult3 : ∀ a b c a′ b′ c′ →
  ((a · b) · c) · ((a′ · b′) · c′) ≡ ((a · a′) · (b · b′)) · (c · c′)
·-mult3 a b c a′ b′ c′ = brute a b c a′ b′ c′
  where
  brute : ∀ a b c a′ b′ c′ →
    ((a · b) · c) · ((a′ · b′) · c′) ≡ ((a · a′) · (b · b′)) · (c · c′)
  brute true  true  true  true  true  true  = refl
  brute true  true  true  true  true  false = refl
  brute true  true  true  true  false true  = refl
  brute true  true  true  true  false false = refl
  brute true  true  true  false true  true  = refl
  brute true  true  true  false true  false = refl
  brute true  true  true  false false true  = refl
  brute true  true  true  false false false = refl
  brute true  true  false true  true  true  = refl
  brute true  true  false true  true  false = refl
  brute true  true  false true  false true  = refl
  brute true  true  false true  false false = refl
  brute true  true  false false true  true  = refl
  brute true  true  false false true  false = refl
  brute true  true  false false false true  = refl
  brute true  true  false false false false = refl
  brute true  false true  true  true  true  = refl
  brute true  false true  true  true  false = refl
  brute true  false true  true  false true  = refl
  brute true  false true  true  false false = refl
  brute true  false true  false true  true  = refl
  brute true  false true  false true  false = refl
  brute true  false true  false false true  = refl
  brute true  false true  false false false = refl
  brute true  false false true  true  true  = refl
  brute true  false false true  true  false = refl
  brute true  false false true  false true  = refl
  brute true  false false true  false false = refl
  brute true  false false false true  true  = refl
  brute true  false false false true  false = refl
  brute true  false false false false true  = refl
  brute true  false false false false false = refl
  brute false true  true  true  true  true  = refl
  brute false true  true  true  true  false = refl
  brute false true  true  true  false true  = refl
  brute false true  true  true  false false = refl
  brute false true  true  false true  true  = refl
  brute false true  true  false true  false = refl
  brute false true  true  false false true  = refl
  brute false true  true  false false false = refl
  brute false true  false true  true  true  = refl
  brute false true  false true  true  false = refl
  brute false true  false true  false true  = refl
  brute false true  false true  false false = refl
  brute false true  false false true  true  = refl
  brute false true  false false true  false = refl
  brute false true  false false false true  = refl
  brute false true  false false false false = refl
  brute false false true  true  true  true  = refl
  brute false false true  true  true  false = refl
  brute false false true  true  false true  = refl
  brute false false true  true  false false = refl
  brute false false true  false true  true  = refl
  brute false false true  false true  false = refl
  brute false false true  false false true  = refl
  brute false false true  false false false = refl
  brute false false false true  true  true  = refl
  brute false false false true  true  false = refl
  brute false false false true  false true  = refl
  brute false false false true  false false = refl
  brute false false false false true  true  = refl
  brute false false false false true  false = refl
  brute false false false false false true  = refl
  brute false false false false false false = refl

------------------------------------------------------------------------
-- Part 1: the elementary interchanger and its dual.

data Side : Set where
  left right : Side

flip : Side → Side
flip left  = right
flip right = left

-- flip when the sign is −1
flipIf : Bool → Side → Side
flipIf true  s = s
flipIf false s = flip s

-- An interchanger-shaped cell between the two composites of the parts
-- of a left operand and a right operand: which operand's part comes
-- first in its source, and which in its target.
record Ich : Set where
  constructor ich
  field
    srcFirst tgtFirst : Side

-- the elementary interchanger: right operand first ⇛ left operand first
canonical : Ich
canonical = ich right left

-- its reverse: left first ⇛ right first
reversed : Ich
reversed = ich left right

-- The action of D_J on the interchanger at (k, l):
--   J (k+1): the k-composition reverses, left and right operands trade
--            names (a relabelling of sides);
--   J (l+1): the l-composition reverses, so in each composite the other
--            part comes first;
--   J (l+2): the cell itself is reversed (source and target swap).
swapIf : Bool → Ich → Ich
swapIf true  c         = c
swapIf false (ich s t) = ich t s

relabel : Bool → Bool → Ich → Ich
relabel a b (ich s t) = ich (flipIf b (flipIf a s)) (flipIf b (flipIf a t))

dualIch : Sign → Nat → Nat → Ich → Ich
dualIch J k l c = swapIf (J (suc (suc l))) (relabel (J (suc k)) (J (suc l)) c)

-- the sign of the row (k, l)
Row : Sign → Nat → Nat → Bool
Row J k l = (J (suc k) · J (suc l)) · J (suc (suc l))

-- The orientation lemma: the dual of the canonical interchanger is
-- canonical when the row is +1 and reversed when it is −1.
dual-canonical : ∀ J k l →
  dualIch J k l canonical ≡ (if Row J k l then canonical else reversed)
dual-canonical J k l with J (suc k) | J (suc l) | J (suc (suc l))
... | true  | true  | true  = refl
... | true  | true  | false = refl
... | true  | false | true  = refl
... | true  | false | false = refl
... | false | true  | true  = refl
... | false | true  | false = refl
... | false | false | true  = refl
... | false | false | false = refl

canonical≢reversed : canonical ≡ reversed → ⊥
canonical≢reversed ()

-- So D_J keeps the interchanger at (k, l) canonical iff the row is +1.
dual-canonical-iff : ∀ J k l →
  (dualIch J k l canonical ≡ canonical) ↔ (Row J k l ≡ true)
dual-canonical-iff J k l = to , from
  where
  to : dualIch J k l canonical ≡ canonical → Row J k l ≡ true
  to h with Row J k l | dual-canonical J k l
  ... | true  | _ = refl
  ... | false | e = ⊥-elim (canonical≢reversed (trans (sym h) e))
  from : Row J k l ≡ true → dualIch J k l canonical ≡ canonical
  from h = trans (dual-canonical J k l) (cong (λ b → if b then canonical else reversed) h)

dual-reversed-iff : ∀ J k l →
  (dualIch J k l canonical ≡ reversed) ↔ (Row J k l ≡ false)
dual-reversed-iff J k l = to , from
  where
  to : dualIch J k l canonical ≡ reversed → Row J k l ≡ false
  to h with Row J k l | dual-canonical J k l
  ... | false | _ = refl
  ... | true  | e = ⊥-elim (canonical≢reversed (trans (sym e) h))
  from : Row J k l ≡ false → dualIch J k l canonical ≡ reversed
  from h = trans (dual-canonical J k l) (cong (λ b → if b then canonical else reversed) h)

------------------------------------------------------------------------
-- Part 2: classification.

-- every row (k, l) with k < l, written l = k + suc d, has sign c
AllRows : Sign → Bool → Set
AllRows J c = ∀ k d → Row J k (k + suc d) ≡ c

-- a duality of the uniform core: every interchanger stays canonical
AllRowsSym : Sign → Set
AllRowsSym J = AllRows J true

-- a duality onto the oplax core: every interchanger is reversed
AllRowsOplax : Sign → Set
AllRowsOplax J = AllRows J false

private
  +1 : ∀ n → n + 1 ≡ suc n
  +1 zero    = refl
  +1 (suc n) = cong suc (+1 n)

  +2 : ∀ n → n + 2 ≡ suc (suc n)
  +2 zero    = refl
  +2 (suc n) = cong suc (+2 n)

  -- the three rows used: (n, n+1), (n, n+2), (n+1, n+2)
  row01 : ∀ J c n → AllRows J c →
    (J (suc n) · J (suc (suc n))) · J (suc (suc (suc n))) ≡ c
  row01 J c n u = subst (λ m → (J (suc n) · J (suc m)) · J (suc (suc m)) ≡ c)
                        (+1 n) (u n 0)

  row02 : ∀ J c n → AllRows J c →
    (J (suc n) · J (suc (suc (suc n)))) · J (suc (suc (suc (suc n)))) ≡ c
  row02 J c n u = subst (λ m → (J (suc n) · J (suc m)) · J (suc (suc m)) ≡ c)
                        (+2 n) (u n 1)

  -- consecutive values agree
  step : ∀ J c n → AllRows J c → J (suc n) ≡ J (suc (suc n))
  step J c n u =
    ·-cancelʳ (J (suc n)) (J (suc (suc n))) (J (suc (suc (suc n))))
      (·-cancelʳ _ _ (J (suc (suc (suc (suc n)))))
        (trans (row02 J c n u) (sym (row01 J c (suc n) u))))

  three : ∀ a → (a · a) · a ≡ a
  three true  = refl
  three false = refl

all-rows↔const : ∀ J c → AllRows J c ↔ (∀ n → J (suc n) ≡ c)
all-rows↔const J c = to , from
  where
  to : AllRows J c → ∀ n → J (suc n) ≡ c
  to u n =
    trans (sym (three (J (suc n))))
      (trans (cong (λ x → (J (suc n) · J (suc n)) · x)
                   (trans (step J c n u) (step J c (suc n) u)))
        (trans (cong (λ x → (J (suc n) · x) · J (suc (suc (suc n))))
                     (step J c n u))
          (row01 J c n u)))
  from : (∀ n → J (suc n) ≡ c) → AllRows J c
  from h k d =
    trans (cong₂ (λ x y → (x · y) · J (suc (suc (k + suc d)))) (h k) (h (k + suc d)))
      (trans (cong (λ z → (c · c) · z) (h (suc (k + suc d))))
             (three c))

-- The headline: J = ∅ is the only symmetry, J = all the only lax/oplax swap.
all-rows-sym↔trivial : ∀ J → AllRowsSym J ↔ (∀ n → J (suc n) ≡ true)
all-rows-sym↔trivial J = all-rows↔const J true

all-rows-oplax↔total : ∀ J → AllRowsOplax J ↔ (∀ n → J (suc n) ≡ false)
all-rows-oplax↔total J = all-rows↔const J false

------------------------------------------------------------------------
-- The rows with k = 0 are the two-tier conditions of GrayDuality.

Level0 : Sign → Bool → Set
Level0 J c = ∀ d → Row J 0 (suc d) ≡ c

private
  -- Const (shift J) from consecutive equalities
  const-from-steps : ∀ J → (∀ d → J (suc (suc d)) ≡ J (suc (suc (suc d)))) →
                     Const (shift J)
  const-from-steps J s zero    = refl
  const-from-steps J s (suc n) = trans (sym (s n)) (const-from-steps J s n)

  steps-from-const : ∀ J → Const (shift J) →
                     ∀ d → J (suc (suc d)) ≡ J (suc (suc (suc d)))
  steps-from-const J c d = trans (c d) (sym (c (suc d)))

  not-inj-eq : ∀ a b → (not a) · b ≡ true → b ≡ not a
  not-inj-eq true  false _ = refl
  not-inj-eq false true  _ = refl
  not-inj-eq true  true  ()
  not-inj-eq false false ()

  not-inj-eq′ : ∀ a b → (not a) · b ≡ false → b ≡ a
  not-inj-eq′ true  true  _ = refl
  not-inj-eq′ false false _ = refl
  not-inj-eq′ true  false ()
  not-inj-eq′ false true  ()

  ·-false : ∀ a b → a · b ≡ false → b ≡ not a
  ·-false true  false _ = refl
  ·-false false true  _ = refl
  ·-false true  true  ()
  ·-false false false ()

  sq-not : ∀ a → (not a) · a ≡ false
  sq-not true  = refl
  sq-not false = refl

  not-not : ∀ a → not (not a) ≡ a
  not-not true  = refl
  not-not false = refl

-- J 1 = +1: the row (0, l) reads J (l+1) · J (l+2); J 1 = −1: its negation.
level0-split : ∀ J → J 1 ≡ true → ∀ d →
  Row J 0 (suc d) ≡ J (suc (suc d)) · J (suc (suc (suc d)))
level0-split J e d = cong (λ x → (x · J (suc (suc d))) · J (suc (suc (suc d)))) e

level0-split′ : ∀ J → J 1 ≡ false → ∀ d →
  Row J 0 (suc d) ≡ (not (J (suc (suc d)))) · J (suc (suc (suc d)))
level0-split′ J e d = cong (λ x → (x · J (suc (suc d))) · J (suc (suc (suc d)))) e

level0↔Symmetry : ∀ J → Level0 J true ↔ Symmetry J
level0↔Symmetry J = to , from
  where
  cls = symmetry-classification J
  to′ : ∀ b → J 1 ≡ b → Level0 J true →
        (J 1 ≡ true × Const (shift J)) ⊎ (J 1 ≡ false × Alt (shift J))
  to′ true  e h = inj₁ (e , const-from-steps J
                    (λ d → ·-true _ _ (trans (sym (level0-split J e d)) (h d))))
  to′ false e h = inj₂ (e , λ n →
                    not-inj-eq (J (suc (suc n))) (J (suc (suc (suc n))))
                      (trans (sym (level0-split′ J e n)) (h n)))
  to : Level0 J true → Symmetry J
  to h = snd cls (to′ (J 1) refl h)
  from : Symmetry J → Level0 J true
  from s d with fst cls s
  ... | inj₁ (e , c) =
        trans (level0-split J e d)
          (trans (cong (λ x → J (suc (suc d)) · x) (sym (steps-from-const J c d)))
                 (·-sq (J (suc (suc d)))))
  ... | inj₂ (e , a) =
        trans (level0-split′ J e d)
          (trans (cong (λ x → not (J (suc (suc d))) · x) (a d))
                 (·-sq (not (J (suc (suc d))))))

level0↔ToOplax : ∀ J → Level0 J false ↔ ToOplax J
level0↔ToOplax J = to , from
  where
  cls = to-oplax-classification J
  to′ : ∀ b → J 1 ≡ b → Level0 J false →
        (J 1 ≡ true × Alt (shift J)) ⊎ (J 1 ≡ false × Const (shift J))
  to′ true  e h = inj₁ (e , λ n →
                    ·-false (J (suc (suc n))) (J (suc (suc (suc n))))
                      (trans (sym (level0-split J e n)) (h n)))
  to′ false e h = inj₂ (e , const-from-steps J (λ d →
                    sym (not-inj-eq′ (J (suc (suc d))) (J (suc (suc (suc d))))
                      (trans (sym (level0-split′ J e d)) (h d)))))
  to : Level0 J false → ToOplax J
  to h = snd cls (to′ (J 1) refl h)
  from : ToOplax J → Level0 J false
  from s d with fst cls s
  ... | inj₁ (e , a) =
        trans (level0-split J e d)
          (trans (cong (λ x → J (suc (suc d)) · x) (a d))
                 (lem (J (suc (suc d)))))
    where
    lem : ∀ x → x · not x ≡ false
    lem true  = refl
    lem false = refl
  ... | inj₂ (e , c) =
        trans (level0-split′ J e d)
          (trans (cong (λ x → not (J (suc (suc d))) · x) (sym (steps-from-const J c d)))
                 (sq-not (J (suc (suc d)))))

------------------------------------------------------------------------
-- All rows = the two-tier test at every shift.

shiftN : Nat → Sign → Sign
shiftN m J n = J (m + n)

private
  +-sucʳ : ∀ m n → m + suc n ≡ suc (m + n)
  +-sucʳ zero    n = refl
  +-sucʳ (suc m) n = cong suc (+-sucʳ m n)

  m+1 : ∀ m → m + 1 ≡ suc m
  m+1 m = trans (+-sucʳ m 0) (cong suc (+0 m))
    where
    +0 : ∀ m → m + 0 ≡ m
    +0 zero    = refl
    +0 (suc m) = cong suc (+0 m)

-- the row (0, d+1) of the m-th shift is the row (m, m+d+1) of J
row-shift : ∀ m J d → Row (shiftN m J) 0 (suc d) ≡ Row J m (m + suc d)
row-shift m J d =
  cong₂ (λ x y → (J x · J y) · J (m + suc (suc (suc d))))
        (m+1 m) (+-sucʳ m (suc d))
  ∙ cong (λ z → (J (suc m) · J (suc (m + suc d))) · J z)
         (trans (+-sucʳ m (suc (suc d))) (cong suc (+-sucʳ m (suc d))))
  where
  infixr 4 _∙_
  _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _∙_ = trans

all-rows↔shifts : ∀ J c → AllRows J c ↔ (∀ m → Level0 (shiftN m J) c)
all-rows↔shifts J c = (λ u m d → trans (row-shift m J d) (u m d))
                   , (λ h k d → trans (sym (row-shift k J d)) (h k d))

-- So a symmetry of the uniform core is a J all of whose shifts are
-- two-tier symmetries (closed-structure.md §D.3's prediction).
all-rows-sym↔shifts-sym : ∀ J → AllRowsSym J ↔ (∀ m → Symmetry (shiftN m J))
all-rows-sym↔shifts-sym J =
    (λ u m → fst (level0↔Symmetry (shiftN m J)) (fst (all-rows↔shifts J true) u m))
  , (λ s → snd (all-rows↔shifts J true) (λ m → snd (level0↔Symmetry (shiftN m J)) (s m)))

all-rows-oplax↔shifts-oplax : ∀ J → AllRowsOplax J ↔ (∀ m → ToOplax (shiftN m J))
all-rows-oplax↔shifts-oplax J =
    (λ u m → fst (level0↔ToOplax (shiftN m J)) (fst (all-rows↔shifts J false) u m))
  , (λ s → snd (all-rows↔shifts J false) (λ m → snd (level0↔ToOplax (shiftN m J)) (s m)))

------------------------------------------------------------------------
-- CaTT's op (reverse the odd dimensions) is the sign pattern alt.

op-two-tier : Symmetry alt
op-two-tier = snd (symmetry-classification alt) (inj₂ (refl , λ n → refl))

-- but at (k, l) = (1, 2) it reverses the uniform interchanger
op-row-1-2 : Row alt 1 2 ≡ false
op-row-1-2 = refl

op-reverses-1-2 : dualIch alt 1 2 canonical ≡ reversed
op-reverses-1-2 = refl

-- co (reverse the even dimensions) already fails two-tier: it is oplax
-- at (0, 1) and lax at (1, 2).
co : Sign
co n = not (alt n)

co-row-0-1 : Row co 0 1 ≡ false
co-row-0-1 = refl

co-row-1-2 : Row co 1 2 ≡ true
co-row-1-2 = refl

------------------------------------------------------------------------
-- The theorem, from the interchangers whose existence is certain.
--
-- GrayRows: the Gray-type interchanger at every level n, i.e. the row
-- (n, n+1), over Σⁿ(ΣD¹ ∨ ΣD¹).  Level0: the two-tier test (the k = 0
-- rows, equivalently Symmetry / ToOplax of GrayDuality).  Together they
-- force J to be constant on dimensions ≥ 1; neither alone does.

GrayRows : Sign → Bool → Set
GrayRows J c = ∀ n → Row J n (suc n) ≡ c

private
  row-const : ∀ J c → (∀ n → J (suc n) ≡ c) → ∀ k l → Row J k l ≡ c
  row-const J c h k l =
    trans (cong₂ (λ x y → (x · y) · J (suc (suc l))) (h k) (h l))
      (trans (cong (λ z → (c · c) · z) (h (suc l))) (three c))

  -- the two-tier symmetries other than ∅ fail a Gray row at level 1 or 2
  alt-rows : ∀ x → ((x · not x) · not (not x) ≡ true) →
             ((not x · not (not x)) · not (not (not x)) ≡ true) → ⊥
  alt-rows true  () _
  alt-rows false _  ()

  alt-rows′ : ∀ x → ((x · not x) · not (not x) ≡ false) →
              ((not x · not (not x)) · not (not (not x)) ≡ false) → ⊥
  alt-rows′ true  _  ()
  alt-rows′ false () _

kernel-theorem : ∀ J c → (GrayRows J c × Level0 J c) ↔ (∀ n → J (suc n) ≡ c)
kernel-theorem J c = to c , from
  where
  from : (∀ n → J (suc n) ≡ c) → GrayRows J c × Level0 J c
  from h = (λ n → row-const J c h n (suc n)) , (λ d → row-const J c h 0 (suc d))

  -- shapes of J from the two-tier classification
  const-case : ∀ c → J 1 ≡ c → Const (shift J) → Row J 1 2 ≡ c → ∀ n → J (suc n) ≡ c
  const-case c e1 cst r zero    = e1
  const-case c e1 cst r (suc n) =
    trans (cst n)
      (trans (sym (three (J 2)))
        (trans (cong₂ (λ y z → (J 2 · y) · z) (sym (cst 1)) (sym (cst 2))) r))

  alt-shape : Alt (shift J) →
    (Row J 1 2 ≡ (J 2 · not (J 2)) · not (not (J 2))) ×
    (Row J 2 3 ≡ (not (J 2) · not (not (J 2))) · not (not (not (J 2))))
  alt-shape a =
    cong₂ (λ y z → (J 2 · y) · z) (a 0) (trans (a 1) (cong not (a 0))) ,
    cong₂ (λ y z → (y · z) · J 5)
          (a 0) (trans (a 1) (cong not (a 0)))
    ∙ cong (λ z → (not (J 2) · not (not (J 2))) · z)
           (trans (a 2) (cong not (trans (a 1) (cong not (a 0)))))
    where
    infixr 4 _∙_
    _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    _∙_ = trans

  to : ∀ c → GrayRows J c × Level0 J c → ∀ n → J (suc n) ≡ c
  to true (g , l0) with fst (symmetry-classification J) (fst (level0↔Symmetry J) l0)
  ... | inj₁ (e1 , cst) = const-case true e1 cst (g 1)
  ... | inj₂ (e1 , a)   = ⊥-elim (alt-rows (J 2)
                            (trans (sym (fst (alt-shape a))) (g 1))
                            (trans (sym (snd (alt-shape a))) (g 2)))
  to false (g , l0) with fst (to-oplax-classification J) (fst (level0↔ToOplax J) l0)
  ... | inj₂ (e1 , cst) = const-case false e1 cst (g 1)
  ... | inj₁ (e1 , a)   = ⊥-elim (alt-rows′ (J 2)
                            (trans (sym (fst (alt-shape a))) (g 1))
                            (trans (sym (snd (alt-shape a))) (g 2)))

-- Neither half suffices.  The Gray rows alone admit J = {1,2,4,5,7,8,…}
-- (reverse n iff 3 ∤ n), which fails the two-tier test; the two-tier
-- test alone admits op (op-two-tier), which fails the Gray row at
-- level 1 (op-row-1-2).
J124 : Sign
J124 zero                   = true
J124 (suc zero)             = false
J124 (suc (suc zero))       = false
J124 (suc (suc (suc n)))    = J124 n

J124-gray-rows : GrayRows J124 true
J124-gray-rows zero                = refl
J124-gray-rows (suc zero)          = refl
J124-gray-rows (suc (suc zero))    = refl
J124-gray-rows (suc (suc (suc n))) = J124-gray-rows n

J124-not-two-tier : Symmetry J124 → ⊥
J124-not-two-tier s with snd (level0↔Symmetry J124) s 2
... | ()

op-gray-rows : GrayRows alt true → ⊥
op-gray-rows g with g 1
... | ()

------------------------------------------------------------------------
-- Part 3: the switches.

-- the two split laws at a level: of a composite left operand (inner
-- law) or of a composite right operand (R)
data Split : Set where
  splitL splitR : Split

otherSplit : Split → Split
otherSplit splitL = splitR
otherSplit splitR = splitL

-- D_J at level k trades left and right operands iff k+1 ∈ J
dualSplit : Sign → Nat → Split → Split
dualSplit J k s = if J (suc k) then s else otherSplit s

has : Switches → Split → Bool
has S splitL = icc S
has S splitR = rsp S

mirrorS : Switches → Switches
mirrorS S = record { icc = rsp S ; rsp = icc S }

dualSetting : Sign → Nat → Switches → Switches
dualSetting J k S = if J (suc k) then S else mirrorS S

-- The dual setting contains exactly the duals of the laws of S.
dual-has : ∀ J k S s → has (dualSetting J k S) (dualSplit J k s) ≡ has S s
dual-has J k S s with J (suc k)
dual-has J k S splitL | true  = refl
dual-has J k S splitR | true  = refl
dual-has J k S splitL | false = refl
dual-has J k S splitR | false = refl

mirror-invol : ∀ S → mirrorS (mirrorS S) ≡ S
mirror-invol S = refl

mirror-vS : mirrorS vS ≡ vS
mirror-vS = refl

mirror-allS : mirrorS allS ≡ allS
mirror-allS = refl

mirror-iccS : mirrorS iccS ≡ rspS
mirror-iccS = refl

mirror-rspS : mirrorS rspS ≡ iccS
mirror-rspS = refl

-- The total duality mirrors the setting at every level; the trivial one
-- fixes it.
total-mirror : ∀ J → (∀ n → J (suc n) ≡ false) → ∀ k S → dualSetting J k S ≡ mirrorS S
total-mirror J h k S = cong (λ b → if b then S else mirrorS S) (h k)

trivial-fixes : ∀ J → (∀ n → J (suc n) ≡ true) → ∀ k S → dualSetting J k S ≡ S
trivial-fixes J h k S = cong (λ b → if b then S else mirrorS S) (h k)

-- A setting is mirror-symmetric iff it is vS or allS.
Symmetric : Switches → Set
Symmetric S = icc S ≡ rsp S

private
  field-icc : ∀ {S S′ : Switches} → S ≡ S′ → icc S ≡ icc S′
  field-icc refl = refl

  mirror-fix→sym : ∀ S → mirrorS S ≡ S → Symmetric S
  mirror-fix→sym S e = sym (field-icc e)

  sym→mirror-fix : ∀ S → Symmetric S → mirrorS S ≡ S
  sym→mirror-fix record { icc = i ; rsp = r } e =
    cong₂ (λ a b → record { icc = a ; rsp = b }) (sym e) e

private
  symDec : ∀ S → Symmetric S ⊎ (Symmetric S → ⊥)
  symDec record { icc = true  ; rsp = true  } = inj₁ refl
  symDec record { icc = false ; rsp = false } = inj₁ refl
  symDec record { icc = true  ; rsp = false } = inj₂ (λ ())
  symDec record { icc = false ; rsp = true  } = inj₂ (λ ())

  choice-inj : ∀ S → (Symmetric S → ⊥) → ∀ a b →
    (if a then S else mirrorS S) ≡ (if b then S else mirrorS S) → a ≡ b
  choice-inj S ns true  true  _ = refl
  choice-inj S ns false false _ = refl
  choice-inj S ns true  false e = ⊥-elim (ns (mirror-fix→sym S (sym e)))
  choice-inj S ns false true  e = ⊥-elim (ns (mirror-fix→sym S e))

-- The dual of one setting is the same at every level iff the setting is
-- symmetric or J (k+1) is independent of k.
level-uniform : ∀ J S →
  (∀ k → dualSetting J k S ≡ dualSetting J 0 S) ↔
  (Symmetric S ⊎ (∀ k → J (suc k) ≡ J 1))
level-uniform J S = to , from
  where
  to : (∀ k → dualSetting J k S ≡ dualSetting J 0 S) →
       Symmetric S ⊎ (∀ k → J (suc k) ≡ J 1)
  to h with symDec S
  ... | inj₁ s  = inj₁ s
  ... | inj₂ ns = inj₂ (λ k → choice-inj S ns (J (suc k)) (J 1) (h k))
  from : Symmetric S ⊎ (∀ k → J (suc k) ≡ J 1) →
         ∀ k → dualSetting J k S ≡ dualSetting J 0 S
  from (inj₁ s) k = trans (both (J (suc k))) (sym (both (J 1)))
    where
    both : ∀ b → (if b then S else mirrorS S) ≡ S
    both true  = refl
    both false = sym→mirror-fix S s
  from (inj₂ c) k = cong (λ b → if b then S else mirrorS S) (c k)
