-- The 2-dimensional cone and cocone shapes (ConesExamples.TermCones2.twoTerm),
-- built by ConeRC / CoconeRC with the generated rc tables layered over RC(1).
-- Every cone and cocone context is run through the certified checker.
-- About 6 min each after the tables are loaded (tools/rc_loop.py regenerates
-- the tables; notes/rc-generator.md).
module CaTTExp.Generated.RCTwoCones where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (build)
open import CaTTExp.Cones
open import CaTTExp.ConeRC
open import CaTTExp.ConesExamples using (okM; module TermCones2)
import CaTTExp.Generated.RCConeTwo as T
import CaTTExp.Generated.RCCoconeTwo as C

cones : all (λ Γ → okM (ConeRC.cone (T.rc orRC rc1) Γ)) TermCones2.twoTerm ≡ true
cones = refl

cocones : all (λ Γ → okM (CoconeRC.cocone (C.rc orRC rc1) Γ)) TermCones2.twoTerm ≡ true
cocones = refl
