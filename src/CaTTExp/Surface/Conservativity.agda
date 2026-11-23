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
-- relation Γ ∣ A ≈T B on raw types and Γ ∣ t ≈t u on raw terms,
-- indexed by the context (for equality of images in the free object
-- on Γ the context matters; for the strictly unital and associative
-- reduction of CaTTExp.SU it does not), and the conversion rule
--
--     Γ ⊢ˢ t : A     A ≈ B     Γ ⊢ˢ B
--     ─────────────────────────────────  (conv)
--               Γ ⊢ˢ t : B
--
-- Its coh rule is the kernel's, except that the head's type is only a
-- surface type and the argument substitution is only surface-typed.
--
-- Main theorem (`conservative`). Assume
--   (E)  in each context, ≈ is an equivalence and a congruence for
--        arr and coh (record SurfaceEq), and it is stable under
--        kernel substitution: Γ ⊢ σ : Δ and Δ ∣ A ≈ A′ give
--        Γ ∣ A[σ] ≈ A′[σ];
--   (SC) the side condition respects ≈ on well-formed kernel heads
--        (`SideResp`);
--   (KC) kernel conversion at a context Γ: if Γ ⊢ t : A in the
--        kernel, Γ ⊢ A′ in the kernel and Γ ∣ A ≈ A′, then the kernel
--        has some t″ with Γ ∣ t″ ≈ t and Γ ⊢ t″ : A′ (`KCAt Γ`).
-- The theorem is local: it uses (KC) only at the context Γ itself and
-- at pasting contexts (where coherence heads are elaborated).
-- Then for every kernel context Γ with KCAt Γ and every kernel type B,
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
-- Deliberate differences from a "bare" surface presentation,
-- documented in the note:
--  * the surface arr rule carries the premise Γ ⊢ˢ A explicitly. In
--    the kernel it is derivable. The surface defined here is therefore
--    a priori a subsystem of the bare one; the two agree given a
--    surface presupposition lemma, which is argued in the note and not
--    formalized;
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
-- (E): the definitional equality of the surface, indexed by the
-- context the terms live in.

record SurfaceEq : Set₁ where
  infix 4 _∣_≈t_ _∣_≈T_
  field
    _∣_≈t_ : Ctx → Tm → Tm → Set
    _∣_≈T_ : Ctx → Ty → Ty → Set

    t-refl  : ∀ {Γ t} → Γ ∣ t ≈t t
    t-sym   : ∀ {Γ t u} → Γ ∣ t ≈t u → Γ ∣ u ≈t t
    t-trans : ∀ {Γ t u v} → Γ ∣ t ≈t u → Γ ∣ u ≈t v → Γ ∣ t ≈t v
    T-refl  : ∀ {Γ A} → Γ ∣ A ≈T A
    T-sym   : ∀ {Γ A B} → Γ ∣ A ≈T B → Γ ∣ B ≈T A
    T-trans : ∀ {Γ A B C} → Γ ∣ A ≈T B → Γ ∣ B ≈T C → Γ ∣ A ≈T C

    arr-cong : ∀ {Γ A A′ t t′ u u′} → Γ ∣ A ≈T A′ → Γ ∣ t ≈t t′ → Γ ∣ u ≈t u′ →
               Γ ∣ arr A t u ≈T arr A′ t′ u′
    -- the head (Δ, A) is compared over its own context Δ, the
    -- arguments over Γ
    coh-cong : ∀ {Γ Δ A A′ σ σ′} → Δ ∣ A ≈T A′ → Pw (Γ ∣_≈t_) σ σ′ →
               Γ ∣ coh Δ A σ ≈t coh Δ A′ σ′

    -- FRV's "substitution" condition, for kernel substitutions.
    stable-T : ∀ {Γ Δ A A′ σ} → Γ ⊢sub σ ∶ Δ → Δ ∣ A ≈T A′ →
               Γ ∣ (A [ σ ]ty) ≈T (A′ [ σ ]ty)

module _ (E : SurfaceEq) where
  open SurfaceEq E

  _∣_≈s_ : Ctx → Sub → Sub → Set
  Γ ∣ σ ≈s σ′ = Pw (Γ ∣_≈t_) σ σ′

  s-sym : ∀ {Γ σ σ′} → Γ ∣ σ ≈s σ′ → Γ ∣ σ′ ≈s σ
  s-sym pw⟨⟩      = pw⟨⟩
  s-sym (pw, p q) = pw, (s-sym p) (t-sym q)

  ----------------------------------------------------------------------
  -- Substituting ≈-related substitutions gives ≈-related results.
  -- (Proved here from congruence; not a hypothesis.)

  private
    pw-len : ∀ {Γ σ σ′} → Γ ∣ σ ≈s σ′ → lenₛ σ ≡ lenₛ σ′
    pw-len pw⟨⟩      = refl
    pw-len (pw, p _) = cong suc (pw-len p)

    lookup-cong : ∀ {Γ σ σ′} i → Γ ∣ σ ≈s σ′ → Γ ∣ lookupₛ σ i ≈t lookupₛ σ′ i
    lookup-cong i pw⟨⟩ = t-refl
    lookup-cong i (pw, {σ} {σ′} p q) rewrite sym (pw-len p) with i ==ℕ lenₛ σ
    ... | true  = q
    ... | false = lookup-cong i p

  mutual
    sub-cong-ty : ∀ {Γ} A {σ σ′} → Γ ∣ σ ≈s σ′ → Γ ∣ (A [ σ ]ty) ≈T (A [ σ′ ]ty)
    sub-cong-ty ⋆           p = T-refl
    sub-cong-ty (arr A t u) p = arr-cong (sub-cong-ty A p) (sub-cong-tm t p) (sub-cong-tm u p)

    sub-cong-tm : ∀ {Γ} t {σ σ′} → Γ ∣ σ ≈s σ′ → Γ ∣ (t [ σ ]tm) ≈t (t [ σ′ ]tm)
    sub-cong-tm (var i)     p = lookup-cong i p
    sub-cong-tm (coh Δ B τ) p = coh-cong T-refl (sub-cong-sub τ p)
    sub-cong-tm (cst k)     p = t-refl

    sub-cong-sub : ∀ {Γ} τ {σ σ′} → Γ ∣ σ ≈s σ′ → Γ ∣ (τ ∘ σ) ≈s (τ ∘ σ′)
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
      convˢ : ∀ {t A B} → Γ ⊢ˢtm t ∶ A → Γ ∣ A ≈T B → Γ ⊢ˢty B → Γ ⊢ˢtm t ∶ B

    data _⊢ˢsub_∶_ (Γ : Ctx) : Sub → Ctx → Set where
      ⟨⟩ˢ : Γ ⊢ctx → Γ ⊢ˢsub ⟨⟩ ∶ ε
      ,ˢ  : ∀ {σ Δ t A} → Γ ⊢ˢsub σ ∶ Δ → Γ ⊢ˢtm t ∶ A [ σ ]ty →
            Γ ⊢ˢsub σ ,ₛ t ∶ Δ ▸ A

  ----------------------------------------------------------------------
  -- (SC) and (KC), the two hypotheses on the kernel.

  -- The side condition of a head is preserved when the head's type is
  -- replaced by a ≈-equal (over Δ) type that is well formed in the
  -- kernel.
  SideResp : Set
  SideResp = ∀ {Δ A t u A′ t′ u′} → Δ ⊢ps → Δ ⊢ty arr A′ t′ u′ →
             Δ ∣ arr A t u ≈T arr A′ t′ u′ →
             T (side Δ A t u) → T (side Δ A′ t′ u′)

  -- Kernel conversion at Γ: a kernel term can be moved to any ≈-equal
  -- kernel type, staying ≈-equal to itself.
  KCAt : Ctx → Set
  KCAt Γ = ∀ {t A A′} → Γ ⊢tm t ∶ A → Γ ⊢ty A′ → Γ ∣ A ≈T A′ →
           Σ Tm λ t″ → (Γ ⊢tm t″ ∶ A′) × (Γ ∣ t″ ≈t t)

  ----------------------------------------------------------------------
  -- The theorem. It is local: (KC) is used at the context of the
  -- judgment and at pasting contexts only.

  module Conservative (side-resp : SideResp)
                      (kc-ps : ∀ {Δ} → Δ ⊢ps → KCAt Δ) where

    -- A kernel arrow type ≈-equal to a surface arrow type.
    record ArrOut (Γ : Ctx) (A : Ty) (t u : Tm) : Set where
      constructor arrOut
      field
        A′ : Ty
        t′ u′ : Tm
        wf : Γ ⊢ty arr A′ t′ u′
        eq : Γ ∣ arr A′ t′ u′ ≈T arr A t u

    mutual
      -- every surface type over Γ is ≈ a kernel type
      elab-ty : ∀ {Γ A} → KCAt Γ → Γ ⊢ˢty A → Σ Ty λ A′ → (Γ ⊢ty A′) × (Γ ∣ A′ ≈T A)
      elab-ty kc (⋆ˢ w) = ⋆ , ⋆-wf w , T-refl
      elab-ty kc (arrˢ dA dt du) with elab-arr kc (arrˢ dA dt du)
      ... | arrOut A′ t′ u′ wf eq = arr A′ t′ u′ , wf , eq

      elab-arr : ∀ {Γ A t u} → KCAt Γ → Γ ⊢ˢty arr A t u → ArrOut Γ A t u
      elab-arr kc (arrˢ dA dt du) with elab-ty kc dA
      ... | A′ , wA , eA with elab-tm kc dt wA (T-sym eA) | elab-tm kc du wA (T-sym eA)
      ...   | t′ , wt , et | u′ , wu , eu =
              arrOut A′ t′ u′ (arr-wf wt wu) (arr-cong eA et eu)

      -- a surface term at a type ≈ to a kernel type B gives a kernel
      -- term of type exactly B; (KC) is used at Γ, and at the pasting
      -- context of each coherence head
      elab-tm : ∀ {Γ t A B} → KCAt Γ → Γ ⊢ˢtm t ∶ A → Γ ⊢ty B → Γ ∣ A ≈T B →
                Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (Γ ∣ t′ ≈t t)
      elab-tm kc (varˢ w e) wB eq = kc (var-wf w e) wB eq
      elab-tm kc (cstˢ w v) wB eq = kc (cst-wf w v) wB eq
      elab-tm kc (convˢ d e _) wB eq = elab-tm kc d wB (T-trans e eq)
      elab-tm kc (cohˢ {Δ} {A} {t} {u} {σ} dps wΔ dT sc dσ) wB eq
        with elab-arr (kc-ps dps) dT | elab-sub kc dσ wΔ
      ... | arrOut A′ t′ u′ wT eT | σ′ , wσ , eσ
        with kc (coh-wf dps wΔ wT (side-resp dps wT (T-sym eT) sc) wσ) wB
                (T-trans (stable-T wσ eT)
                  (T-trans (sub-cong-ty (arr A t u) eσ) eq))
      ...   | t″ , w″ , e″ = t″ , w″ , t-trans e″ (coh-cong eT eσ)

      -- a surface substitution into a kernel context gives a kernel
      -- substitution
      elab-sub : ∀ {Γ σ Δ} → KCAt Γ → Γ ⊢ˢsub σ ∶ Δ → Δ ⊢ctx →
                 Σ Sub λ σ′ → (Γ ⊢sub σ′ ∶ Δ) × (Γ ∣ σ′ ≈s σ)
      elab-sub kc (⟨⟩ˢ w) _ = ⟨⟩ , ⟨⟩-wf w , pw⟨⟩
      elab-sub kc (,ˢ {σ} {Δ} {t} {A} dσ dt) (▸-wf wΔ wA) with elab-sub kc dσ wΔ
      ... | σ′ , wσ , eσ with elab-tm kc dt (ty[] closed wA wσ) (sub-cong-ty A (s-sym eσ))
      ...   | t′ , wt , et = (σ′ ,ₛ t′) , ,-wf wσ wt , pw, eσ et

    -- Conservativity at Γ: given (KC) at Γ (and at pasting contexts),
    -- a surface derivation of a kernel type gives a kernel term of that
    -- type, ≈-equal to the surface term.
    conservative : ∀ {Γ t B} → KCAt Γ → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                   Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (Γ ∣ t′ ≈t t)
    conservative kc wB d = elab-tm kc d wB T-refl

    -- The global form: (KC) everywhere gives conservativity everywhere.
    conservative-everywhere : (∀ {Γ} → KCAt Γ) →
                              ∀ {Γ t B} → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                              Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (Γ ∣ t′ ≈t t)
    conservative-everywhere kc = conservative kc

    -- In particular, the surface inhabits no kernel type the kernel
    -- leaves empty.
    no-new-inhabitants : ∀ {Γ t B} → KCAt Γ → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                         Σ Tm λ t′ → Γ ⊢tm t′ ∶ B
    no-new-inhabitants kc wB d with conservative kc wB d
    ... | t′ , w , _ = t′ , w

  ----------------------------------------------------------------------
  -- The converse: conservativity forces relative coherence.
  --
  -- EL ("≈-relative coherence") at Γ: parallel kernel terms that are
  -- ≈-equal are connected by a kernel cell that is ≈ to an identity.
  -- If the surface is conservative at Γ and the kernel has identities,
  -- EL holds at Γ: take the identity on u, convert its type u → u to
  -- u → u′, and apply conservativity.

  -- The conclusion of `conservative`, as a property of a context.
  ConservativeAt : Ctx → Set
  ConservativeAt Γ = ∀ {t B} → Γ ⊢ty B → Γ ⊢ˢtm t ∶ B →
                     Σ Tm λ t′ → (Γ ⊢tm t′ ∶ B) × (Γ ∣ t′ ≈t t)

  -- Every kernel derivation is a surface derivation (given the
  -- kernel's presupposition, which the explicit premise of arrˢ needs).
  module Embed (presup : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A) where
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

    -- A surface that identifies the two ends of a kernel cell whose
    -- reverse type is empty in the kernel is not conservative there.
    reverse-breaks : ∀ {Γ A u u′ c} → Γ ⊢tm c ∶ arr A u u′ → Γ ⊢tm u′ ∶ A →
                     Γ ⊢tm u ∶ A → Γ ∣ u ≈t u′ →
                     (∀ t → ¬ (Γ ⊢tm t ∶ arr A u′ u)) → ¬ ConservativeAt Γ
    reverse-breaks {u = u} {u′} dc du′ du eq empty cons
      with cons (arr-wf du′ du)
                (convˢ (emb-tm dc) (arr-cong T-refl eq (t-sym eq)) (emb-ty (arr-wf du′ du)))
    ... | t , dt , _ = empty t dt

  module Converse
    -- the kernel's presupposition (holds for the empty signature,
    -- CaTTExp.Derived.tm-ty) and its identities
    (presup : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A)
    (identity : ∀ {Γ u A} → Γ ⊢tm u ∶ A → Σ Tm λ i → Γ ⊢tm i ∶ arr A u u)
    where

    open Embed presup public

    -- EL at Γ, with the "≈ identity" half: the connecting cell is ≈ to
    -- the kernel's identity on u.
    RelCohAt : Ctx → Set
    RelCohAt Γ = ∀ {A u u′} (du : Γ ⊢tm u ∶ A) → Γ ⊢tm u′ ∶ A → Γ ∣ u ≈t u′ →
                 Σ Tm λ e → (Γ ⊢tm e ∶ arr A u u′) × (Γ ∣ e ≈t fst (identity du))

    necessary : ∀ {Γ} → ConservativeAt Γ → RelCohAt Γ
    necessary cons {A} {u} {u′} du du′ eq with identity du
    ... | i , di with cons (arr-wf du du′)
                          (convˢ (emb-tm di) (arr-cong T-refl t-refl eq) (emb-ty (arr-wf du du′)))
    ...   | e , de , ee = e , de , ee

------------------------------------------------------------------------
-- Non-vacuity: syntactic equality satisfies every hypothesis, and the
-- surface then derives exactly the kernel's judgments. This is a
-- sanity check of the statement, not the instance of interest.

module Trivial where

  trivialEq : SurfaceEq
  trivialEq = record
    { _∣_≈t_ = λ _ → _≡_ ; _∣_≈T_ = λ _ → _≡_
    ; t-refl = refl ; t-sym = sym ; t-trans = trans
    ; T-refl = refl ; T-sym = sym ; T-trans = trans
    ; arr-cong = λ { refl refl refl → refl }
    ; coh-cong = λ { refl p → cong (coh _ _) (pw≡ p) }
    ; stable-T = λ { _ refl → refl }
    }
    where
    pw≡ : ∀ {σ σ′} → Pw _≡_ σ σ′ → σ ≡ σ′
    pw≡ pw⟨⟩ = refl
    pw≡ (pw, p refl) = cong (_,ₛ _) (pw≡ p)

  side-resp : SideResp trivialEq
  side-resp _ _ refl sc = sc

  kc : ∀ {Γ} → KCAt trivialEq Γ
  kc {t = t} d _ refl = t , d , refl

  open Conservative trivialEq side-resp (λ _ → kc) public
