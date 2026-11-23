-- Test harness for scripts/sigp_check/check.sh (not part of the --safe library).
module DumpSigP where

open import CaTTExp.Prelude
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import CaTTExp.Uniform.SigP

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}

infixr 5 _&_
_&_ : String → String → String
_&_ = primStringAppend

cmpN : CmpOp → String
cmpN chiO = "chi"
cmpN rO = "r"
cmpN tO = "t"
cmpN iotaO = "iota"
cmpN hO = "h"

sh : Tm → String
sh (v d x) = x
sh (sF n x) = "(s" & primShowNat n & " " & sh x & ")"
sh (tF n x) = "(t" & primShowNat n & " " & sh x & ")"
sh (idT n x) = "(id" & primShowNat n & " " & sh x & ")"
sh (comp n x y) = "(comp" & primShowNat n & " " & sh x & " " & sh y & ")"
sh (lft k n x y) = "(left" & primShowNat k & "_" & primShowNat n & " " & sh x & " " & sh y & ")"
sh (rgt k n x y) = "(right" & primShowNat k & "_" & primShowNat n & " " & sh x & " " & sh y & ")"
sh (cmp o x y) = "(" & cmpN o & " " & sh x & " " & sh y & ")"

joinS : String → List String → String
joinS sep [] = ""
joinS sep (x ∷ []) = x
joinS sep (x ∷ xs) = x & sep & joinS sep xs

mapS : ∀ {A : Set} → (A → String) → List A → List String
mapS f [] = []
mapS f (x ∷ xs) = f x ∷ mapS f xs

shVar : Tm → String
shVar t = sh t & ":" & primShowNat (dim t)

shG : Guard → String
shG (l , r) = sh l & "=" & sh r

shS : Schema → String
shS (schema n vs gs l r) = "EQ " & n & "|" & joinS "," (mapS shVar vs) & "|" & joinS ";" (mapS shG gs) & "|" & sh l & "|" & sh r

shR : Schema → String
shR (schema n vs gs l r) = "RULE " & n & "|" & joinS "," (mapS shVar vs) & "|" & joinS ";" (mapS shG gs) & "|" & sh l & "|" & sh r

shO : OpSpec → String
shO (opSpec n as gs ap s t) = "OP " & n & "|" & joinS ";" (mapS shG gs) & "|" & sh s & "|" & sh t

main : IO ⊤
main = putStrLn (joinS "\n" (mapS shO (operationsUpTo 4) ++ mapS shS (equationsUpTo 4) ++ mapS shR rules))
