------------------------------------------------------------------------
-- Compiled checks of the generic horns of HornGen.Gen (ledger S27 (e′))
-- at levels the `refl` suite in CaTTExp.Lim.HornGenExamples cannot
-- afford (n = 2 over every 1-dimensional test diagram takes well over
-- an hour by `refl`). The program runs the certified checkers
-- CaTTExp.Check.checkCtx (plain CaTT) and CaTTExp.Gray.Pure.checkCtx
-- (CaTT_L), compiled by the GHC backend. The postulates below are only
-- the GHC bindings for printing; the program proves nothing in Agda.
--
--   cd tools/agda-run
--   agda --compile --compile-dir=/tmp/cattexp-run HornGenRun.agda
--   /tmp/cattexp-run/HornGenRun
--
-- Each line prints P:T / L:T when the horn context J₂ is well formed in
-- CaTT / CaTT_L. Compiling and running takes about a minute and a half;
-- all eight lines print P:T L:T (Arr at n = 3 did not finish in 25 min).
------------------------------------------------------------------------
module HornGenRun where
open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
import CaTTExp.Gray.Pure as L
open import CaTTExp.Lim.HornGen
open import CaTTExp.Lim.HornGenExamples using (Arr; Pt; Cospan; Par; Comp; Loop)
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
_<>_ = primStringAppend
b2s : Bool → String
b2s true = "T"
b2s false = "F"

J2G : Ctx → Nat → Maybe Ctx
J2G Γ n = hornDataGen Γ n >>= λ d → just (HornData.J2 d)

okP okL : Maybe Ctx → Bool
okP (just Γ) = is-just (checkCtx Γ)
okP nothing  = false
okL (just Γ) = is-just (L.checkCtx Γ)
okL nothing  = false

line : String → Ctx → Nat → IO ⊤
line nm Γ n = putStrLn (nm <> " n=" <> primShowNat n <> " P:" <> b2s (okP (J2G Γ n)) <> " L:" <> b2s (okL (J2G Γ n)))

main : IO ⊤
main = line "Arr" Arr 0 >> (line "Arr" Arr 1 >> (line "Arr" Arr 2 >> (line "Cospan" Cospan 1 >> (line "Loop" Loop 2 >> (line "Par" Par 2 >> (line "Comp" Comp 2 >> line "Pt" Pt 3))))))
