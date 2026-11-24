------------------------------------------------------------------------
-- Compiled checks of the conical transfors at level 2 over the
-- 2-dimensional diagrams (ledger B18). Evaluating these contexts to
-- CaTT syntax by `refl` takes about 25 minutes per shape
-- (CaTTExp.ConesTr2Slow does the loop), so this program runs the same
-- certified checker, CaTTExp.Check.checkCtx, compiled by the GHC
-- backend. The postulates below are only the GHC bindings for printing;
-- the program proves nothing in Agda: it prints the checker's verdict.
--
--   cd tools/agda-run
--   agda --compile --compile-dir=/tmp/cattexp-run ConesTr2Run.agda
--   /tmp/cattexp-run/ConesTr2Run
--
-- For each context it prints whether it is defined and, if so, the
-- length of the longest prefix the checker accepts.
------------------------------------------------------------------------
module ConesTr2Run where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import Agda.Builtin.String
open import Agda.Builtin.IO

postulate
  putStrLn : String → IO ⊤
  _>>_     : IO ⊤ → IO ⊤ → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as T
import qualified System.IO #-}
{-# COMPILE GHC putStrLn = \s -> T.putStrLn s >> System.IO.hFlush System.IO.stdout #-}
{-# COMPILE GHC _>>_ = (>>) #-}

infixr 5 _<>_
_<>_ : String → String → String
_<>_ = primStringAppend

diskTy : Nat → ExTy
diskTy zero    = ob
diskTy (suc j) = hom (diskTy j) (v (j + j)) (v (suc (j + j)))

DiskEx : Nat → ExCtx
DiskEx n = concatMap (λ j → diskTy j ∷ diskTy j ∷ []) (range n) ++ (diskTy n ∷ [])

Loop Par2 : ExCtx
Loop = ob ∷ hom ob (v 0) (v 0) ∷ hom (hom ob (v 0) (v 0)) (v 1) (v 1) ∷ []
Par2 = DiskEx 2 ++ (hom (hom ob (v 0) (v 1)) (v 2) (v 3) ∷ [])

take : Nat → ExCtx → ExCtx
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

-- The prefix of length n of K, checked (its types are evaluated in K).
okPrefix : ExCtx → Nat → Bool
okPrefix K n = is-just (checkCtx (evCtxGo K (take n K) ε))

verdict : ExCtx → Nat → ExCtx → String
verdict K i []       = "well typed, " <> primShowNat i <> " variables"
verdict K i (A ∷ As) =
  if okPrefix K (suc i) then verdict K (suc i) As
  else ("REJECTED at variable " <> primShowNat i)

report : String → Maybe Ctrf → IO ⊤
report nm nothing  = putStrLn (nm <> ": undefined")
report nm (just T) = putStrLn (nm <> ": " <> verdict (Ctrf.ctx T) 0 (Ctrf.ctx T))

main : IO ⊤
main =
  report "Tr2 over D2"            (ctrf 2 (DiskEx 2)) >>
  (report "Tr2 over loop"         (ctrf 2 Loop) >>
  (report "Tr2 over 2 par. 2-cells" (ctrf 2 Par2) >>
  (report "coTr2 over D2"         (coctrf 2 (DiskEx 2)) >>
  (report "coTr2 over loop"       (coctrf 2 Loop) >>
  (report "coTr2 over 2 par. 2-cells" (coctrf 2 Par2) >>
   putStrLn ("Tr3 over D2: " <> (if is-just (ctrf 3 (DiskEx 2))
                                  then "built (not checked: its top type has about 31000 nodes)"
                                  else "undefined")))))))
