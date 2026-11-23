------------------------------------------------------------------------
-- Operation heads in the form of spec §1.1 (ledger S27 (b)): a head h
-- has an arity *context* Γ_h and a type A_h over it, both written with
-- ordinary variables, and
--
--   Δ ⊢ σ : Γ_h    Valid(h)
--   ─────────────────────── (op)
--   Δ ⊢ h[σ] : A_h[σ]
--
-- In CaTTExp.Binder a head is a binder with an empty telescope whose
-- argument telescope and result type are Γ_h and A_h *closed*: every
-- variable j turned into the bound variable `bvar 0 j` (`clTel 0`,
-- `clTy 0`). This module proves that the binder rule at such a former is
-- exactly (op):
--
--  * open-cl: opening the closure of A with arguments ts is A[ts], so
--  * args⇔sub: Δ ⊢args ts ∶ clTel 0 Γ_h  iff  Δ ⊢sub ts ∶ Γ_h, and
--  * op-intro / op-inv: the binder rule at h[σ] is (op), both ways.
--
-- `HonestAt b y G A` says that the former b at selector y is the head
-- with arity G and type A; `honest-head` shows such a former is a head
-- in the sense of CaTTExp.Binder.Heads (closed data), so substitution,
-- the checker and its completeness cover it, and HeadOK for it is
-- G ⊢ A (`honest-ok`). A closed constant c : A is the case G = ε.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.HonestHeads (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Heads 𝕊 using (HeadAt)

-- Closing (clTy, clTel, …), Honest, and opening the closure (open-cl*).
open import CaTTExp.Binder.Close K B public

------------------------------------------------------------------------
-- The former b at selector y is the head with arity G and type A: its
-- side condition asks for the empty telescope, and its argument
-- telescope and result type are the closures of G and A.
record HonestAt (b : B) (y : Nat) (G : Ctx) (A : Ty) : Set where
  field
    honest  : Honest G
    ty-sc   : T (scTy? (len G) A)
    ty-lc   : T (lcTy? 0 A)
    side-ε  : ∀ Δ → T (bside b y Δ) → Δ ≡ ε
    args-eq : bargs b y ε ≡ clTel 0 G
    res-eq  : bres b y ε ≡ clTy 0 A

-- An honest former is a head in the sense of CaTTExp.Binder.Heads, as
-- soon as every selector of it is honest.
honest-head : ∀ {b} → (∀ y → T (bside b y ε) → Σ Ctx λ G → Σ Ty λ A → HonestAt b y G A) →
              (∀ y Δ → T (bside b y Δ) → Δ ≡ ε) → HeadAt b
honest-head {b} h ε-only y Δ p with ε-only y Δ p
... | refl with h y p
...   | G , A , ha =
  tt , subst (λ Θ → T (scTel? 0 Θ)) (sym (HonestAt.args-eq ha)) (sc-clTel 0 G)
     , subst (λ X → T (scTy? 0 X)) (sym (HonestAt.res-eq ha)) (sc-clTy 0 A)

------------------------------------------------------------------------
-- Typing.

module Typed
  (side : Ctx → Ty → Tm → Tm → Bool)
  (mark : Ctx → BM.Mark → Tm → Bool)
  where

  open import CaTTExp.Binder.TypingWith 𝕊 side mark
  open import CaTTExp.Binder.Scoping 𝕊 side mark

  -- Arguments for the closure of an honest context are substitutions
  -- into it, and conversely.
  args→sub : ∀ {Γ ts} G → Honest G → Γ ⊢args ts ∶ clTel 0 G → Γ ⊢sub ts ∶ G
  args→sub ε _ (⟨⟩-a w) = ⟨⟩-wf w
  args→sub {Γ} (G ▸[ ms ] A) (hG , sA , lA) (,-a {ts} {t = t} a d o) =
    ,-wf (args→sub G hG a)
         (subst (Γ ⊢tm t ∶_) (open-clTy 0 ts A (args-lc a) sA′ lA) d)
         o
    where
    len-eq : ∀ {ts Θ} → Γ ⊢args ts ∶ Θ → lenₛ ts ≡ len Θ
    len-eq (⟨⟩-a _)    = refl
    len-eq (,-a a _ _) = cong suc (len-eq a)
    len-eq′ : lenₛ ts ≡ len G
    len-eq′ = trans (len-eq a) (len-clTel 0 G)
    sA′ : T (scTy? (lenₛ ts) A)
    sA′ = subst (λ n → T (scTy? n A)) (sym len-eq′) sA

  sub→args : ∀ {Γ ts} G → Honest G → Γ ⊢sub ts ∶ G → Γ ⊢args ts ∶ clTel 0 G
  sub→args ε _ (⟨⟩-wf w) = ⟨⟩-a w
  sub→args {Γ} (G ▸[ ms ] A) (hG , sA , lA) (,-wf {ts} {t = t} s d o) =
    ,-a (sub→args G hG s)
        (subst (Γ ⊢tm t ∶_) (sym (open-clTy 0 ts A (sub-lc s) sA′ lA)) d)
        o
    where
    len-eq : ∀ {ts Θ} → Γ ⊢sub ts ∶ Θ → lenₛ ts ≡ len Θ
    len-eq (⟨⟩-wf _)    = refl
    len-eq (,-wf s _ _) = cong suc (len-eq s)
    sA′ : T (scTy? (lenₛ ts) A)
    sA′ = subst (λ n → T (scTy? n A)) (sym (len-eq s)) sA

  private
    len-sub : ∀ {Γ ts G} → Γ ⊢sub ts ∶ G → lenₛ ts ≡ len G
    len-sub (⟨⟩-wf _)    = refl
    len-sub (,-wf s _ _) = cong suc (len-sub s)

  -- The rule (op) of spec §1.1 is the binder rule at an honest former.
  op-intro : ∀ {Γ b y G A σ} → HonestAt b y G A → T (bside b y ε) →
             Γ ⊢ctx → Γ ⊢sub σ ∶ G → Γ ⊢tm bnd b y ε σ ∶ A [ σ ]ty
  op-intro {Γ} {b} {y} {G} {A} {σ} ha ok w s =
    subst (Γ ⊢tm bnd b y ε σ ∶_)
      (trans (cong (opTy 0 σ) (HonestAt.res-eq ha))
             (open-clTy 0 σ A (sub-lc s)
                (subst (λ n → T (scTy? n A)) (sym (len-sub s)) (HonestAt.ty-sc ha))
                (HonestAt.ty-lc ha)))
      (bnd-wf tt tt w ok
        (subst (Γ ⊢args σ ∶_) (sym (HonestAt.args-eq ha)) (sub→args G (HonestAt.honest ha) s)))

  -- Inversion: every derivation of h[σ] is an instance of (op).
  op-inv : ∀ {Γ b y G A σ X} → HonestAt b y G A →
           Γ ⊢tm bnd b y ε σ ∶ X →
           T (bside b y ε) × Γ ⊢sub σ ∶ G × (X ≡ A [ σ ]ty)
  op-inv {Γ} {b} {y} {G} {A} {σ} ha (bnd-wf _ _ _ ok as) =
    ok , s
       , trans (cong (opTy 0 σ) (HonestAt.res-eq ha))
               (open-clTy 0 σ A (sub-lc s)
                  (subst (λ n → T (scTy? n A)) (sym (len-sub s)) (HonestAt.ty-sc ha))
                  (HonestAt.ty-lc ha))
    where
    s : Γ ⊢sub σ ∶ G
    s = args→sub G (HonestAt.honest ha) (subst (Γ ⊢args σ ∶_) (HonestAt.args-eq ha) as)

  ----------------------------------------------------------------------
  -- HeadOK (CaTTExp.Binder.Heads) at an honest former is Γ_h ⊢ A_h.

  open import CaTTExp.Binder.Rename 𝕊 side mark using (id-ty)
  import CaTTExp.Binder.Heads 𝕊 as Hd
  open Hd.Typed side mark using (arity; resTy)

  open-cl-id : ∀ G → Honest G → openTel 0 (clTel 0 G) ≡ G
  open-cl-id ε             _              = refl
  open-cl-id (G ▸[ ms ] A) (hG , sA , lA) =
    cong₂ (_▸[ ms ]_) (open-cl-id G hG)
      (trans (open-clTy 0 (fresh 0 (len (clTel 0 G))) A (lc-fresh 0 (len (clTel 0 G))) sA′ lA)
             (id-ty (len (clTel 0 G)) A sA″))
    where
    sA″ : T (scTy? (len (clTel 0 G)) A)
    sA″ = subst (λ n → T (scTy? n A)) (sym (len-clTel 0 G)) sA
    sA′ : T (scTy? (lenₛ (fresh 0 (len (clTel 0 G)))) A)
    sA′ = subst (λ n → T (scTy? n A)) (sym (lenₛ-fresh 0 (len (clTel 0 G)))) sA″

  honest-ok : ∀ {b y G A} → HonestAt b y G A → G ⊢ty A →
              ∀ Δ → T (bside b y Δ) → arity b y Δ ⊢ty resTy b y Δ
  honest-ok {b} {y} {G} {A} ha a Δ p with HonestAt.side-ε ha Δ p
  ... | refl
    rewrite HonestAt.args-eq ha | HonestAt.res-eq ha | open-cl-id G (HonestAt.honest ha) =
    subst (G ⊢ty_) (sym eq) a
    where
    sA : T (scTy? (len (clTel 0 G)) A)
    sA = subst (λ n → T (scTy? n A)) (sym (len-clTel 0 G)) (HonestAt.ty-sc ha)
    eq : opTy 0 (fresh 0 (len (clTel 0 G))) (clTy 0 A) ≡ A
    eq = trans (open-clTy 0 (fresh 0 (len (clTel 0 G))) A (lc-fresh 0 (len (clTel 0 G)))
                  (subst (λ n → T (scTy? n A)) (sym (lenₛ-fresh 0 (len (clTel 0 G)))) sA)
                  (HonestAt.ty-lc ha))
               (id-ty (len (clTel 0 G)) A sA)
