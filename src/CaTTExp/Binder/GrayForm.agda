------------------------------------------------------------------------
-- The object formers of the Gray biclosed structure (spec §8.1,
-- (GB-form); §1.6's head table, chapter 8 row) as a binder interface
-- (ledger S26g):
--
--   Γ ⊢ A : ⋆    Γ ⊢ B : ⋆
--   ─────────────────────────────────────────────── (GB-form)
--   Γ ⊢ A ⊗ B : ⋆     Γ ⊢ A\B : ⋆     Γ ⊢ B/A : ⋆
--
-- Each former is an operation head with arity context (A B : ⋆) and
-- type ⋆, so it is a binder with an empty telescope and selector 0,
-- like the destructors of CaTTExp.Binder.Des:
--
--   tensor   A ⊗ B   = bnd tensor 0 ε (A, B)
--   lhom     A\C     = bnd lhom   0 ε (A, C)   (evaluation (A, A\C ▸ C))
--   rhom     C/A     = bnd rhom   0 ε (C, A)   (evaluation (C/A, A ▸ C))
--
-- The arguments are listed in the order the formula is written, so
-- the first argument of lhom is the bound object A and the first of
-- rhom is the codomain C (`notes/conventions.md` §3.2).
--
-- Scope. These are the object formers only. Their universal
-- properties (the corollas m, e^ℓ, e^r and the cut templates of §8.2–
-- 8.3) are stated over the *multimap* judgment (X₁, …, Xₙ ▸ Z), which
-- is not a judgment of the binder kernel: a multimap with n ≠ 1 inputs
-- is not a kernel term. They are formalized over their own syntax in
-- CaTTExp.Gray.Biclosed; CaTTExp.Binder.GrayFormEmbed sends that
-- syntax's object formulas to kernel object terms built with these
-- formers. Implementing the multimap judgment in the kernel is the
-- open item of spec §8.1 ("Status").
--
-- There are no equations: A ⊗ B is a term former, not a definition.
-- The construction is over any set B of formers into which these
-- inject (`inj`), so that they can sit beside other binders.
-- `grayFormBinders` is the three formers alone.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Embed using (Binders)

module CaTTExp.Binder.GrayForm where

data GBKind : Set where
  tensorK lhomK rhomK : GBKind

data GBF : Set where
  gb : GBKind → GBF

pattern tensor = gb tensorK
pattern lhom   = gb lhomK
pattern rhom   = gb rhomK

_==G_ : GBF → GBF → Bool
gb tensorK ==G gb tensorK = true
gb lhomK   ==G gb lhomK   = true
gb rhomK   ==G gb rhomK   = true
_          ==G _          = false

==G-sound : ∀ b c → T (b ==G c) → b ≡ c
==G-sound (gb tensorK) (gb tensorK) _ = refl
==G-sound (gb lhomK)   (gb lhomK)   _ = refl
==G-sound (gb rhomK)   (gb rhomK)   _ = refl
==G-sound (gb tensorK) (gb lhomK)   ()
==G-sound (gb tensorK) (gb rhomK)   ()
==G-sound (gb lhomK)   (gb tensorK) ()
==G-sound (gb lhomK)   (gb rhomK)   ()
==G-sound (gb rhomK)   (gb tensorK) ()
==G-sound (gb rhomK)   (gb lhomK)   ()

==G-refl : ∀ b → T (b ==G b)
==G-refl (gb tensorK) = tt
==G-refl (gb lhomK)   = tt
==G-refl (gb rhomK)   = tt

------------------------------------------------------------------------
-- The construction.

module GrayFormConstruction (K B : Set) (inj : GBF → B) where

  open Syntax K B

  isε : Ctx → Bool
  isε ε = true
  isε _ = false

  -- The arity context (A B : ⋆), written with bound variables (it
  -- mentions none).
  argsG : Ctx
  argsG = ε ▸ ⋆ ▸ ⋆

  side : GBF → Nat → Ctx → Bool
  side _ y Δ = (y ==ℕ 0) ∧ isε Δ

  args : GBF → Nat → Ctx → Ctx
  args _ _ _ = argsG

  res : GBF → Nat → Ctx → Ty
  res _ _ _ = ⋆

  -- The formers applied to two object terms.
  gbApp : GBKind → Tm → Tm → Tm
  gbApp k a b = bnd (inj (gb k)) 0 ε (⟨⟩ ,ₛ a ,ₛ b)

  _⊗ᵗ_ _\\ᵗ_ _//ᵗ_ : Tm → Tm → Tm
  a ⊗ᵗ b  = gbApp tensorK a b
  a \\ᵗ c = gbApp lhomK a c
  c //ᵗ a = gbApp rhomK c a

grayFormBinders : (K : Set) → Binders K
grayFormBinders K = record
  { B         = GBF
  ; _==B_     = _==G_
  ; ==B-sound = ==G-sound
  ; bside     = side
  ; bargs     = args
  ; bres      = res
  }
  where open GrayFormConstruction K GBF (λ b → b)
