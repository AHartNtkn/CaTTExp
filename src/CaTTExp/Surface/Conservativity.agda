------------------------------------------------------------------------
-- Conservativity of a surface language with definitional equality
-- over a CaTT-style kernel, reduced to one lemma about the kernel
-- (ledger item S19 (a), (b); notes/surface-conservativity.md §2–§3).
--
-- The kernel is TypingWith 𝕊 side: any CaTT-style theory whose coh
-- rule has a side condition on its own head (plain CaTT, two-tier L,
-- uniform L relative to its layers). It has no conversion rule.
--
-- The surface has the kernel's rules plus definitional equality: a
-- relation _≈T_ on raw types and _≈t_ on raw terms (for instance the
-- strictly unital and associative reduction of CaTTExp.SU, closed
-- under symmetry), and the conversion rule
--
--     Γ ⊢ˢ t : A     A ≈ B     Γ ⊢ˢ B
--     ─────────────────────────────────  (conv)
--               Γ ⊢ˢ t : B
--
-- Its coh rule is the kernel's, except that the head's type is only a
-- surface type and the argument substitution is only surface-typed.
--
-- Main theorem (`conservative`). Assume
--   (E)  ≈ is an equivalence and a congruence for arr and coh
--        (record SurfaceEq), and stable under substitution
--        (A ≈ A′ ⇒ A[σ] ≈ A′[σ]);
--   (SC) the side condition respects ≈ on well-formed kernel heads
--        (`SideResp`);
--   (KC) kernel conversion: if Γ ⊢ t : A in the kernel, Γ ⊢ A′ in the
--        kernel and A ≈ A′, then the kernel has some t″ ≈ t with
--        Γ ⊢ t″ : A′ (`KernelConv`).
-- Then for every kernel context Γ and kernel type B,
--
--     Γ ⊢ˢ t : B   implies   Γ ⊢ t′ : B for some kernel term t′ ≈ t,
--
-- and every surface type over Γ is ≈ to a kernel type over Γ. The
-- proof is by induction on surface derivations and computes t′, so it
-- is also the elaborator.
--
-- What this module does NOT prove: (KC) and (SC) for any particular
-- kernel and relation. For the strict-associator/unitor surface they
-- are the open content of S19 (b); see the note, §3–§4, where (KC) is
-- reduced to relative coherence of ≈-equal parallel terms. The
-- instance at the bottom (≈ is syntactic equality) only shows the
-- hypotheses are satisfiable; it is not the instance of interest.
--
-- Deliberate differences from a "bare" surface presentation, both
-- harmless and documented in the note:
--  * the surface arr rule carries the premise Γ ⊢ˢ A explicitly (in
--    the kernel it is derivable; on the surface it would otherwise
--    need a presupposition lemma for conv);
--  * the context Γ is a kernel context (conservativity is a statement
--    about kernel judgments).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Subst as SubstM

module CaTTExp.Surface.Conservativity
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (closed : SubstM.Closed 𝕊 side)
  where

open Signature 𝕊
open import CaTTExp.TypingWith 𝕊 side
open SubstM 𝕊 side using (ty[]; sub-ctx)

------------------------------------------------------------------------
-- Pointwise extension of a relation on terms to substitutions.

data Pw (R : Tm → Tm → Set) : Sub → Sub → Set where
  pw⟨⟩ : Pw R ⟨⟩ ⟨⟩
  pw,  : ∀ {σ σ′ t t′} → Pw R σ σ′ → R t t′ → Pw R (σ ,ₛ t) (σ′ ,ₛ t′)

------------------------------------------------------------------------
-- (E): the definitional equality of the surface.

record SurfaceEq : Set₁ where
  field
    _≈t_ : Tm → Tm → Set
    _≈T_ : Ty → Ty → Set

    t-refl  : ∀ {t} → t ≈t t
    t-sym   : ∀ {t u} → t ≈t u → u ≈t t
    t-trans : ∀ {t u v} → t ≈t u → u ≈t v → t ≈t v
    T-refl  : ∀ {A} → A ≈T A
    T-sym   : ∀ {A B} → A ≈T B → B ≈T A
    T-trans : ∀ {A B C} → A ≈T B → B ≈T C → A ≈T C

    arr-cong : ∀ {A A′ t t′ u u′} → A ≈T A′ → t ≈t t′ → u ≈t u′ →
               arr A t u ≈T arr A′ t′ u′
    coh-cong : ∀ {Δ A A′ σ σ′} → A ≈T A′ → Pw _≈t_ σ σ′ →
               coh Δ A σ ≈t coh Δ A′ σ′

    -- FRV's "substitution" condition on the rule set R.
    stable-T : ∀ {A A′} σ → A ≈T A′ → (A [ σ ]ty) ≈T (A′ [ σ ]ty)

module _ (E : SurfaceEq) where
  open SurfaceEq E

  _≈s_ : Sub → Sub → Set
  _≈s_ = Pw _≈t_

  s-refl : ∀ {σ} → σ ≈s σ
  s-refl {⟨⟩}     = pw⟨⟩
  s-refl {σ ,ₛ t} = pw, s-refl t-refl

  s-sym : ∀ {σ σ′} → σ ≈s σ′ → σ′ ≈s σ
  s-sym pw⟨⟩        = pw⟨⟩
  s-sym (pw, p q)   = pw, (s-sym p) (t-sym q)

  ----------------------------------------------------------------------
  -- Substituting ≈-related substitutions gives ≈-related results.
  -- (Proved here from congruence; not a hypothesis.)

  private
    pw-len : ∀ {σ σ′} → σ ≈s σ′ → lenₛ σ ≡ lenₛ σ′
    pw-len pw⟨⟩      = refl
    pw-len (pw, p _) = cong suc (pw-len p)

    lookup-cong : ∀ {σ σ′} i → σ ≈s σ′ → lookupₛ σ i ≈t lookupₛ σ′ i
    lookup-cong i pw⟨⟩ = t-refl
    lookup-cong i (pw, {σ} {σ′} p q) rewrite sym (pw-len p) with i ==ℕ lenₛ σ
    ... | true  = q
    ... | false = lookup-cong i p

  mutual
    sub-cong-ty : ∀ A {σ σ′} → σ ≈s σ′ → (A [ σ ]ty) ≈T (A [ σ′ ]ty)
    sub-cong-ty ⋆           p = T-refl
    sub-cong-ty (arr A t u) p = arr-cong (sub-cong-ty A p) (sub-cong-tm t p) (sub-cong-tm u p)

    sub-cong-tm : ∀ t {σ σ′} → σ ≈s σ′ → (t [ σ ]tm) ≈t (t [ σ′ ]tm)
    sub-cong-tm (var i)     p = lookup-cong i p
    sub-cong-tm (coh Δ B τ) p = coh-cong T-refl (sub-cong-sub τ p)
    sub-cong-tm (cst k)     p = t-refl

    sub-cong-sub : ∀ τ {σ σ′} → σ ≈s σ′ → (τ ∘ σ) ≈s (τ ∘ σ′)
    sub-cong-sub ⟨⟩       p = pw⟨⟩
    sub-cong-sub (τ ,ₛ t) p = pw, (sub-cong-sub τ p) (sub-cong-tm t p)

  ----------------------------------------------------------------------
  -- The surface judgments: the kernel's rules, plus (conv).

  infix 4 _⊢ˢty_ _⊢ˢtm_∶_ _⊢ˢsub_∶_

  mutual
    data _⊢ˢty_ (Γ : Ctx) : Ty → Set where
      ⋆ˢ   : Γ ⊢ctx → Γ ⊢ˢty ⋆
      arrˢ : ∀ {A t u} → Γ ⊢ˢty A → Γ ⊢ˢtm t ∶ A → Γ ⊢ˢtm u ∶ A →
             Γ ⊢ˢty arr A t u

    data _⊢ˢtm_∶_ (Γ : Ctx) : Tm → Ty → Set where
      varˢ  : ∀ {i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ˢtm var i ∶ A
      cohˢ  : ∀ {Δ A t u σ} →
              Δ ⊢ps → Δ ⊢ctx → Δ ⊢ˢty arr A t u →
              T (side Δ A t u) →
              Γ ⊢ˢsub σ ∶ Δ →
              Γ ⊢ˢtm coh Δ (arr A t u) σ ∶ (arr A t u) [ σ ]ty
      cstˢ  : ∀ {k} → Γ ⊢ctx → Valid k → Γ ⊢ˢtm cst k ∶ ty k
      convˢ : ∀ {t A B} → Γ ⊢ˢtm t ∶ A → A ≈T B → Γ ⊢ˢty B → Γ ⊢ˢtm t ∶ B

    data _⊢ˢsub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
      ⟨⟩ˢ : Γ ⊢ctx → Γ ⊢ˢsub ⟨⟩ ∶ ε
      ,ˢ  : ∀ {σ Δ t A} → Γ ⊢ˢsub σ ∶ Δ → Γ ⊢ˢtm t ∶ A [ σ ]ty →
            Γ ⊢ˢsub σ ,ₛ t ∶ Δ ▸ A

  ----------------------------------------------------------------------
  -- (SC) and (KC), the two hypotheses on the kernel.

  -- The side condition of a head is preserved when the head's type is
  -- replaced by a ≈-equal type that is well formed in the kernel.
  SideResp : Set
  SideResp = ∀ {Δ A t u A′ t′ u′} → Δ ⊢ps → Δ ⊢ty arr A′ t′ u′ →
             arr A t u ≈T arr A′ t′ u′ →
             T (side Δ A t u) → T (side Δ A′ t′ u′)

  -- Kernel conversion: a kernel term can be moved to any ≈-equal
  -- kernel type, staying ≈-equal to itself.
  KernelConv : Set
  KernelConv = ∀ {Γ t A A′} → Γ ⊢tm t ∶ A → Γ ⊢ty A′ → A ≈T A′ →
               Σ Tm λ t″ → (Γ ⊢tm t″ ∶ A′) × (t″ ≈t t)

  ----------------------------------------------------------------------
  -- The theorem.

  module Conservative (side-resp : SideResp) (kc : KernelConv) where

    -- A kernel arrow type ≈-equal to a surface arrow type.
    record ArrOut (Γ : Ctx) (A : Ty) (t u : Tm) : Set where
      constructor arrOut
      field
        A′ : Ty
        t′ u′ : Tm
        wf : Γ ⊢ty arr A′ t′ u′
        eq : arr A′ t′ u′ ≈T arr A t u

    mutual
      -- every surface type over a kernel context is ≈ a kernel type
      elab-ty : ∀ {Γ A} → Γ ⊢ˢty A → Σ Ty λ A′ → (Γ ⊢ty A′) × (A′ ≈T A)
      elab-ty (⋆ˢ w) = ⋆ , ⋆-wf w , T-refl
      elab-ty (arrˢ dA dt du) with elab-arr (arrˢ dA dt du)
      ... | arrOut A′ t′ u′ wf eq = arr A′ t′ u′ , wf , eq

      elab-arr : ∀ {Γ A t u} → Γ ⊢ˢty arr A t u → ArrOut Γ A t u
      elab-arr (arrˢ dA dt du) with elab-ty dA
      ... | A′ , wA , eA with elab-tm dt wA (T-sym eA) | elab-tm du wA (T-sym eA)
      ...   | t′ , wt , et | u′ , wu , eu =
              arrOut A′ t′ u′ (arr-wf wt wu) (arr-cong eA et eu)

      -- a surface term at a type ≈ to a kernel type B gives a kernel
      -- term of type exactly B
      elab-tm : ∀ {Γ t A B} → Γ ⊢ˢtm t ∶ A → Γ ⊢ty B → A ≈T B →
                Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (t′ ≈t t)
      elab-tm (varˢ w e) wB eq = kc (var-wf w e) wB eq
      elab-tm (cstˢ w v) wB eq = kc (cst-wf w v) wB eq
      elab-tm (convˢ d e _) wB eq = elab-tm d wB (T-trans e eq)
      elab-tm {Γ} (cohˢ {Δ} {A} {t} {u} {σ} dps wΔ dT sc dσ) wB eq
        with elab-arr dT | elab-sub dσ wΔ
      ... | arrOut A′ t′ u′ wT eT | σ′ , wσ , eσ
        with kc (coh-wf dps wΔ wT (side-resp dps wT (T-sym eT) sc) wσ) wB
                (T-trans (sub-cong-ty (arr A′ t′ u′) eσ)
                  (T-trans (stable-T σ eT) eq))
      ...   | t″ , w″ , e″ = t″ , w″ , t-trans e″ (coh-cong eT eσ)

      -- a surface substitution into a kernel context gives a kernel
      -- substitution
      elab-sub : ∀ {Γ σ Δ} → Γ ⊢ˢsub σ ∶ Δ → Δ ⊢ctx →
                 Σ Sub λ σ′ → (Γ ⊢sub σ′ ∶ Δ) × (σ′ ≈s σ)
      elab-sub (⟨⟩ˢ w) _ = ⟨⟩ , ⟨⟩-wf w , pw⟨⟩
      elab-sub (,ˢ {σ} {Δ} {t} {A} dσ dt) (▸-wf wΔ wA) with elab-sub dσ wΔ
      ... | σ′ , wσ , eσ with elab-tm dt (ty[] closed wA wσ) (sub-cong-ty A (s-sym eσ))
      ...   | t′ , wt , et = (σ′ ,ₛ t′) , ,-wf wσ wt , pw, eσ et

    -- Conservativity: over a kernel context, a surface derivation of a
    -- kernel type gives a kernel term of that type.
    conservative : ∀ {Γ t B} → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                   Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (t′ ≈t t)
    conservative wB d = elab-tm d wB T-refl

    -- In particular, the surface inhabits no kernel type the kernel
    -- leaves empty.
    no-new-inhabitants : ∀ {Γ t B} → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                         Σ Tm λ t′ → Γ ⊢tm t′ ∶ B
    no-new-inhabitants wB d with conservative wB d
    ... | t′ , w , _ = t′ , w

  ----------------------------------------------------------------------
  -- The converse: conservativity forces relative coherence.
  --
  -- EL ("≈-relative coherence"): parallel kernel terms that are ≈-equal
  -- are connected by a kernel cell. If the surface is conservative and
  -- the kernel has identities, EL holds: take the identity on u, convert
  -- its type u → u to u → u′, and apply conservativity. So the
  -- hypothesis (KC) cannot be dropped: (KC) follows from EL plus
  -- whiskering (note §3.2), and EL follows from conservativity.

  -- The conclusion of `conservative`, as a property of a context.
  ConservativeAt : Ctx → Set
  ConservativeAt Γ = ∀ {t B} → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                     Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (t′ ≈t t)

  RelCohAt : Ctx → Set
  RelCohAt Γ = ∀ {A u u′} → Γ ⊢tm u ∶ A → Γ ⊢tm u′ ∶ A → u ≈t u′ →
               Σ Tm λ e → Γ ⊢tm e ∶ arr A u u′

  module Converse
    -- the kernel's presupposition (holds for the empty signature,
    -- CaTTExp.Derived.tm-ty) and its identities
    (presup : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A)
    (identity : ∀ {Γ u A} → Γ ⊢tm u ∶ A → Σ Tm λ i → Γ ⊢tm i ∶ arr A u u)
    where

    mutual
      emb-ty : ∀ {Γ A} → Γ ⊢ty A → Γ ⊢ˢty A
      emb-ty (⋆-wf w)     = ⋆ˢ w
      emb-ty (arr-wf d e) = arrˢ (emb-ty (presup d)) (emb-tm d) (emb-tm e)

      emb-tm : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ˢtm t ∶ A
      emb-tm (var-wf w e)           = varˢ w e
      emb-tm (coh-wf p w dA sc dσ)  = cohˢ p w (emb-ty dA) sc (emb-sub dσ)
      emb-tm (cst-wf w v)           = cstˢ w v

      emb-sub : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → Γ ⊢ˢsub σ ∶ Δ
      emb-sub (⟨⟩-wf w)  = ⟨⟩ˢ w
      emb-sub (,-wf s d) = ,ˢ (emb-sub s) (emb-tm d)

    necessary : ∀ {Γ} → ConservativeAt Γ → RelCohAt Γ
    necessary cons {A} {u} {u′} du du′ eq with identity du
    ... | i , di =
      let wB  = arr-wf du du′
          conv = convˢ (emb-tm di) (arr-cong T-refl t-refl eq) (emb-ty wB)
      in fst (cons wB conv) , fst (snd (cons wB conv))

------------------------------------------------------------------------
-- Non-vacuity: syntactic equality satisfies every hypothesis, and the
-- surface then derives exactly the kernel's judgments. This is a
-- sanity check of the statement, not the instance of interest.

module Trivial where
  open import CaTTExp.Prelude

  trivialEq : SurfaceEq
  trivialEq = record
    { _≈t_ = _≡_ ; _≈T_ = _≡_
    ; t-refl = refl ; t-sym = sym ; t-trans = trans
    ; T-refl = refl ; T-sym = sym ; T-trans = trans
    ; arr-cong = λ { refl refl refl → refl }
    ; coh-cong = λ { refl p → cong (coh _ _) (pw≡ p) }
    ; stable-T = λ { σ refl → refl }
    }
    where
    pw≡ : ∀ {σ σ′} → Pw _≡_ σ σ′ → σ ≡ σ′
    pw≡ pw⟨⟩ = refl
    pw≡ (pw, p refl) = cong (_,ₛ _) (pw≡ p)

  side-resp : SideResp trivialEq
  side-resp _ _ refl sc = sc

  kc : KernelConv trivialEq
  kc {t = t} d _ refl = t , d , refl

  open Conservative trivialEq side-resp kc public
