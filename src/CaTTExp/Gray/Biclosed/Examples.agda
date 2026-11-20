------------------------------------------------------------------------
-- D7d: checks by evaluation of the templates of F.7.4.
--
-- For every row below and every dimension in range, the generated
-- generic context is well formed, both goals (c and ε) are well typed
-- in it (Typing.wtGoal / wf), and admit? accepts both.  For directed
-- templates, at every gap of H, admit? rejects the reversed goal, and
-- a context whose ball b is made invertible admits no directed goal.
-- The derived rules of F.7.4 item 5 ((lhom), E.2's unit and fill) are
-- admitted instances.  Negative controls show the checker rejects
-- ill-typed and non-generic variants.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Examples where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates

------------------------------------------------------------------------
-- Rows (generic, canonically numbered)

-- (U, V ▸ Z) against (U ⊗ V ▸ Z), with a context entry on the left
pair₁ : Row
pair₁ = pairR (obj 0 ∷ []) (obj 1) (obj 2) [] (obj 3)

-- B ⊗ ⟦D¹⟧: a probe in the pair (left of a lax cylinder, E.2)
pair₂ : Row
pair₂ = pairR [] (obj 0) (rep (disk 1)) [] (obj 1)

-- probe pairing ⟦Δ⟧, ⟦Θ⟧ against ⟦Δ ⊠ Θ⟧
probe₁ : Row
probe₁ = probeR (obj 0 ∷ []) (named 0) (named 1) [] (obj 1)

-- unit: (X, ⟦D⁰⟧ ▸ Z) against (X ▸ Z)
unit₁ : Row
unit₁ = unitR (obj 0 ∷ []) [] (obj 1)

-- left evaluation, Φ = (X): Φ ▸ A\C against A, Φ ▸ C
evL₁ : Row
evL₁ = evLR (obj 1 ∷ []) (obj 0) (obj 2)

-- left evaluation with a time slot in Φ: Φ = (X, ⟦D¹⟧)
evL₂ : Row
evL₂ = evLR (obj 1 ∷ rep (disk 1) ∷ []) (obj 0) (obj 2)

-- right evaluation, Φ = (X)
evR₁ : Row
evR₁ = evRR (obj 0 ∷ []) (obj 1) (obj 2)

-- (lhom): Δ ⊳ [Θ, C] = (⟦Δ⟧ ▸ C/⟦Θ⟧); a probe as bound argument
lhom : Row
lhom = evRR (rep (named 0) ∷ []) (rep (named 1)) (obj 0)

-- E.2 unit u_B : B → [Θ, B ⊗ Θ]: the right row with A = ⟦Θ⟧
e2-unit : Row
e2-unit = evRR (obj 0 ∷ []) (rep (named 0)) (obj 1)

rows : List Row
rows = pair₁ ∷ pair₂ ∷ probe₁ ∷ unit₁ ∷ evL₁ ∷ evL₂ ∷ evR₁ ∷ lhom ∷ e2-unit ∷ []

------------------------------------------------------------------------
-- Checks

upto : Nat → List Nat
upto zero    = zero ∷ []
upto (suc n) = upto n ++ (suc n ∷ [])

hArity : Row → Nat
hArity ρ = length (ins (H ρ))

reverseTop : CTy → CTy
reverseTop (hom m g A s t) = hom m g A t s
reverseTop A               = A

-- turn the ball b (last entry) invertible: no directed hypothesis left
invertLast : Ctx → Ctx
invertLast []                          = []
invertLast (hom dir g A s t ∷ [])      = hom inv g A s t ∷ []
invertLast (x ∷ [])                    = x ∷ []
invertLast (x ∷ y ∷ xs)                = x ∷ invertLast (y ∷ xs)

good : Tmpl → Bool
good t = okT t ∧ wtGoal (ctx t) (cgoal t) ∧ wf (ctx t) (egoal t)
       ∧ admit? (ctx t) (cgoal t) ∧ admit? (ctx t) (egoal t)

goodDir : Tmpl → Bool
goodDir t = good t
          ∧ not (admit? (ctx t) (reverseTop (cgoal t)))
          ∧ not (admit? (invertLast (ctx t)) (cgoal t))

cutOK : Row → Nat → Bool
cutOK ρ n = good (tmpl ρ (hArity ρ) inv n)

dcutOK : Row → Nat → Bool
dcutOK ρ k = all (λ g → goodDir (tmpl ρ g dir (suc k))) (upto (hArity ρ))

-- (GB-cut) at n = 0, 1, 2 for every row
check-cut : T (all (λ ρ → all (cutOK ρ) (upto 2)) rows)
check-cut = tt

-- (GB-dcut) at k = 1, 2, at every gap, for every row
check-dcut : T (all (λ ρ → all (dcutOK ρ) (upto 1)) rows)
check-dcut = tt

-- one deeper instance of each kind
check-cut3 : T (cutOK evL₂ 3)
check-cut3 = tt

------------------------------------------------------------------------
-- Negative controls

-- a non-generic formula (a compound in a variable position) is rejected
nongeneric : Row
nongeneric = evLR ((obj 1 ⊗ obj 2) ∷ []) (obj 0) (obj 3)

control-nongeneric : T (not (admit? (ctx (tmpl nongeneric 1 inv 0))
                                   (cgoal (tmpl nongeneric 1 inv 0))))
control-nongeneric = tt

-- a badly numbered generic row is rejected
badnum : Row
badnum = evLR (obj 0 ∷ []) (obj 1) (obj 2)

control-badnum : T (not (admit? (ctx (tmpl badnum 1 inv 0)) (cgoal (tmpl badnum 1 inv 0))))
control-badnum = tt

-- directed n = 0 is not a template
control-dir0 : T (not (okT (tmpl evL₁ 1 dir 0)))
control-dir0 = tt

-- the checker rejects a cell between endpoints of the wrong type
control-type : T (not (wf (ctx (tmpl evL₁ 1 inv 1))
                          (hom inv 1 (op (H evL₁)) (var (bM 0)) (var (uP 0)))))
control-type = tt

-- the ε goal with its collar dropped is not well typed at n = 1
control-collar : T (not (wf (ctx (tmpl evL₁ 1 inv 1))
                            (hom inv 2 (tyRU (tmpl evL₁ 1 inv 1) 1)
                               (rmap evL₁ (here (cgoal (tmpl evL₁ 1 inv 1))))
                               (var (pos 1 0)))))
control-collar = tt

-- one outer operation b : (A, X ▸ C) admits both curries at n = 0:
-- left (X ▸ A\C) and right (A ▸ C/X).  The two n = 0 contexts coincide.
check-both-curries : T (admit? (ctx (tmpl evL₁ 1 inv 0)) (cgoal (tmpl evL₁ 1 inv 0))
                      ∧ admit? (ctx (tmpl evL₁ 1 inv 0)) (cgoal (tmpl evR₁ 1 inv 0)))
check-both-curries = tt

-- at n = 1 the contexts differ (the sphere u has type H), and the goal
-- of one row is not admitted in the context of the other
control-cross : T (not (admit? (ctx (tmpl evR₁ 1 inv 1)) (cgoal (tmpl evL₁ 1 inv 1))))
control-cross = tt
