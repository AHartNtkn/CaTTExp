------------------------------------------------------------------------
-- Runs Checks.VCompLift compiled (MAlonzo). Not part of the --safe
-- library: it needs IO. Usage: tools/vcomp-check/run.sh
--
--   diskOK sd m : the certified checker accepts the disk image for D^m
--   typeOK sd m : its raw type is the required one (no derivation)
------------------------------------------------------------------------
module Main where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import CaTTExp.GrayCtx.CylGen using (Side; right; left)
open import CaTTExp.GrayCtx.Checks.VCompLift

postulate
  putStrLn : String → IO ⊤
  bindIO   : {A B : Set} → IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}
{-# COMPILE GHC bindIO = \ _ _ -> (>>=) #-}

infixr 1 _>>_
_>>_ : IO ⊤ → IO ⊤ → IO ⊤
a >> b = bindIO a λ _ → b

showB : Bool → String
showB true  = "true"
showB false = "false"

sdS : Side → String
sdS right = "right"
sdS left  = "left"

line : String → Side → Nat → Bool → IO ⊤
line what sd m b = putStrLn (primStringAppend what (primStringAppend " " (primStringAppend (sdS sd)
  (primStringAppend " D^" (primStringAppend (primShowNat m) (primStringAppend ": " (showB b)))))))

main : IO ⊤
main =
  line "typeOK" left 3 (typeOK left 3) >> line "typeOK" right 3 (typeOK right 3) >>
  line "typeOK" left 4 (typeOK left 4) >> line "typeOK" right 4 (typeOK right 4) >>
  line "diskOK" left 0 (diskOK left 0) >> line "diskOK" right 0 (diskOK right 0) >>
  line "diskOK" left 1 (diskOK left 1) >> line "diskOK" right 1 (diskOK right 1) >>
  line "diskOK" left 2 (diskOK left 2) >> line "diskOK" right 2 (diskOK right 2) >>
  line "diskOK" left 3 (diskOK left 3) >> line "diskOK" right 3 (diskOK right 3)
