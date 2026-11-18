-- Executable harness (not part of the --safe library): runs the
-- certified checker, compiled, on the associator construction.
module RunAssoc where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Free.Builders
open import CaTTExp.Free.AssociatorDepth2
import CaTTExp.Free.LeftUnitorDepth2 as LU
open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤
  _>>_     : IO ⊤ → IO ⊤ → IO ⊤
infixr 1 _>>_
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}
{-# COMPILE GHC _>>_ = (>>) #-}

mutual
  szTy : Ty → Nat
  szTy ⋆ = 1
  szTy (arr A t u) = suc (szTy A + szTm t + szTm u)
  szTm : Tm → Nat
  szTm (var _) = 1
  szTm (coh Γ A σ) = suc (szCtx Γ + szTy A + szSub σ)
  szTm (cst _) = 1
  szCtx : Ctx → Nat
  szCtx ε = 1
  szCtx (Γ ▸ A) = suc (szCtx Γ + szTy A)
  szSub : Sub → Nat
  szSub ⟨⟩ = 1
  szSub (σ ,ₛ t) = suc (szSub σ + szTm t)

postulate showN : Nat → String
{-# COMPILE GHC showN = \n -> Data.Text.pack (show n) #-}
{-# FOREIGN GHC import qualified Data.Text #-}

showB : Bool → String
showB true  = "true"
showB false = "false"


line : String → Bool → IO ⊤
line s b = putStrLn (primStringAppend s (showB b))

main : IO ⊤
main =
  putStrLn (primStringAppend "size of K-α (syntax nodes): " (showN (szTm (fst K-α)))) >>
  line "L well typed: " (checks Lad L) >>
  line "R well typed: " (checks Lad R) >>
  go 1 steps >>
  line "K-α checks with its computed type: " (checks Lad K-α) >>
  line "computed type is L → R: " (snd K-α ==Ty K-α-type) >>
  line "negative control, reversed type R → L: " (checks Lad (fst K-α , arr (snd L) (fst R) (fst L))) >>
  line "consistency control, left unitor K-λ: " (checks LU.Sq LU.K-λ)
  where
  go : Nat → List TT → IO ⊤
  go _ []       = putStrLn "all steps done"
  go n (s ∷ ss) = line (primStringAppend "step " (primStringAppend (showN n) ": ")) (checks Lad s) >> go (suc n) ss
