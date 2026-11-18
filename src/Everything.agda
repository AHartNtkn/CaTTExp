{-# OPTIONS --guardedness #-}
-- Typecheck this file to check the whole development.
module Everything where

import CaTTExp.Prelude
import CaTTExp.Syntax
import CaTTExp.Signature
import CaTTExp.Pasting
import CaTTExp.TypingWith
import CaTTExp.Typing
import CaTTExp.Subst
import CaTTExp.PastingTrees
import CaTTExp.CheckWith
import CaTTExp.Check
import CaTTExp.PastingCheck
import CaTTExp.Completeness
import CaTTExp.ConstSub
import CaTTExp.Weakening
import CaTTExp.Suspension
import CaTTExp.GroupModel
import CaTTExp.Pure
import CaTTExp.PureMetatheory
import CaTTExp.Examples
import CaTTExp.Sketch.Representables
import CaTTExp.Sketch.NonDerivable
import CaTTExp.Free.Reflect
import CaTTExp.Free.Builders
import CaTTExp.Free.Cylinder
import CaTTExp.Free.LeftUnitorDepth2
import CaTTExp.Gray.Support
import CaTTExp.Gray.Typing
import CaTTExp.Gray.Check
import CaTTExp.Gray.Pure
import CaTTExp.Gray.Examples
import CaTTExp.Gray.Cube
import CaTTExp.Lim.Named
import CaTTExp.Lim.Conditions
import CaTTExp.Lim.Rules
import CaTTExp.Lim.Terms
import CaTTExp.Lim.Defects
import CaTTExp.Lim.Repaired
import CaTTExp.Gray.Bounded
import CaTTExp.Lim.Linearity
import CaTTExp.GraphFiller
import CaTTExp.GraphFillerExamples
import CaTTExp.GrayDuality
