------------------------------------------------------------------------
-- Forgetting marks. A derivation of TypingWith 𝕊 side mark is a
-- derivation of TypingWith 𝕊 side (λ _ _ _ → true): the mark premises
-- (`marksOK`) become trivial and nothing else changes. On the
-- mark-free instance MarkRen, MarkSub and MarkVar hold trivially, so
-- Binder.Subst applies to it. Facts that never read a mark premise
-- (dimensions, supports, fuel stability of a mark judgment) can be
-- proved there and pulled back to any marked instance.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.TypingWith
import CaTTExp.Binder.Rename
import CaTTExp.Binder.Subst

module CaTTExp.Binder.Forget
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊

noMark : Ctx → BM.Mark → Tm → Bool
noMark _ _ _ = true

module R (mark : Ctx → BM.Mark → Tm → Bool) = CaTTExp.Binder.TypingWith 𝕊 side mark
module F = CaTTExp.Binder.TypingWith 𝕊 side noMark

all-true : ∀ (ms : List BM.Mark) → T (all (λ _ → true) ms)
all-true []       = tt
all-true (_ ∷ ms) = all-true ms

module _ (mark : Ctx → BM.Mark → Tm → Bool) where
  private module M = R mark

  mutual
    forget-ctx : ∀ {Γ} → Γ M.⊢ctx → Γ F.⊢ctx
    forget-ctx M.ε-wf       = F.ε-wf
    forget-ctx (M.▸-wf w a) = F.▸-wf (forget-ctx w) (forget-ty a)

    forget-ty : ∀ {Γ A} → Γ M.⊢ty A → Γ F.⊢ty A
    forget-ty (M.⋆-wf w)     = F.⋆-wf (forget-ctx w)
    forget-ty (M.arr-wf d e) = F.arr-wf (forget-tm d) (forget-tm e)

    forget-tm : ∀ {Γ t A} → Γ M.⊢tm t ∶ A → Γ F.⊢tm t ∶ A
    forget-tm (M.var-wf w eq)             = F.var-wf (forget-ctx w) eq
    forget-tm (M.coh-wf p w a ok s)       = F.coh-wf p (forget-ctx w) (forget-ty a) ok (forget-sub s)
    forget-tm (M.cst-wf w v)              = F.cst-wf (forget-ctx w) v
    forget-tm (M.bnd-wf sc lc w ok as)    = F.bnd-wf sc lc (forget-ctx w) ok (forget-args as)

    forget-sub : ∀ {Γ σ Δ} → Γ M.⊢sub σ ∶ Δ → Γ F.⊢sub σ ∶ Δ
    forget-sub (M.⟨⟩-wf w)        = F.⟨⟩-wf (forget-ctx w)
    forget-sub (M.,-wf {ms = ms} s d _) = F.,-wf (forget-sub s) (forget-tm d) (all-true ms)

    forget-args : ∀ {Γ ts Θ} → Γ M.⊢args ts ∶ Θ → Γ F.⊢args ts ∶ Θ
    forget-args (M.⟨⟩-a w)        = F.⟨⟩-a (forget-ctx w)
    forget-args (M.,-a {ms = ms} a d _) = F.,-a (forget-args a) (forget-tm d) (all-true ms)

------------------------------------------------------------------------
-- The mark-free instance satisfies the mark hypotheses.

module FR = CaTTExp.Binder.Rename 𝕊 side noMark
module FS = CaTTExp.Binder.Subst 𝕊 side noMark

markRenF : FR.MarkRen
markRenF _ _ _ = tt

markSubF : FS.MarkSub
markSubF _ _ _ = tt

markVarF : FS.MarkVar
markVarF {Γ} {i} _ _ = all-true (marksAt Γ i)
