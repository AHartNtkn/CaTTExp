------------------------------------------------------------------------
-- The limit rules over two-tier L (B7, first slice), checked against
-- the L core (CaTTExp.Gray.*, PR #26) and notes/limits-metatheory.md
-- §5.2–§5.3.
--
-- The shared schema has P and L differ only in which comparison
-- variables of the transfor shapes are marked declarations:
--   P: those over every positive-dimensional diagram generator;
--   L: those over *marked* diagram generators only (coherent marking).
-- Here this switch is implemented for the cone-morphism shapes of
-- Repaired.agda (n = 1, diagrams of dimension ≤ 1), and checked on the
-- collapse instance.
--
--  O1  The collapse instance (an arbitrary 3-cell z over the diagram
--      1_Y, Repaired.agda) is also well typed in the L core.
--  O2  Under L with f unmarked, m_f is not marked, so the instance is
--      admitted with no certificate (CertSubL, typed by the L core):
--      unrestricted lax transfors. Under P it is rejected
--      (Repaired.collapse-instance-rejected).
--  O3  Under L with f marked, m_f is marked, and the instance is
--      rejected unless z is certified, exactly as under P.
--  O4  The reverse interchanger N⁻¹ cannot be formed as a coh in L, in
--      any context and for any substitution (Gray.Examples.no-ich⁻).
--      Cited, not formalized here: that the image comparison F(β)_f of
--      a cell β under the universal cone is the interchanger over
--      ΣD¹ ∨ ΣD¹ substituted by (β, λ_f) (limits-metatheory.md §5.2),
--      so the researcher's inverse R⁻¹ = B ; N⁻¹ ; A⁻¹ is not available
--      by coherence. That *no* term of L inverts it is Thm 1(2), open.
------------------------------------------------------------------------
module CaTTExp.Lim.OverL where

open import CaTTExp.Prelude
import CaTTExp.Gray.Pure as L
import CaTTExp.Gray.Examples as LEx
open import CaTTExp.Pure using (Tm; Ty; Sub; Ctx; coh; arr; _[_]tm)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Repaired
open import CaTTExp.Lim.Defects using (Γarr)

------------------------------------------------------------------------
-- Named contexts and substitutions, type-checked by the L core.

record SubOKL (Ω : NCtx) (θ : Sub) (M : NCtx) : Set where
  constructor subokL
  field
    coreΩ    : Ctx
    coreM    : Ctx
    coreθ    : Sub
    lowersΩ  : lower Ω ≡ just coreΩ
    lowersM  : lower M ≡ just coreM
    lowersθ  : renSub (levelOf Ω) θ ≡ just coreθ
    wfΩ      : coreΩ L.⊢ctx
    wfM      : coreM L.⊢ctx
    derived  : coreΩ L.⊢sub coreθ ∶ coreM

subL? : (Ω : NCtx) (θ : Sub) (M : NCtx) → Maybe (SubOKL Ω θ M)
subL? Ω θ M = go (lower Ω) refl (lower M) refl (renSub (levelOf Ω) θ) refl
  where
  go : (a : Maybe Ctx) → lower Ω ≡ a → (b : Maybe Ctx) → lower M ≡ b →
       (c : Maybe Sub) → renSub (levelOf Ω) θ ≡ c → Maybe (SubOKL Ω θ M)
  go (just LΩ) e₁ (just LM) e₂ (just σ) e₃ =
    L.checkCtx LΩ >>= λ w → L.checkCtx LM >>= λ wM → L.checkSub LΩ w σ LM >>= λ d →
    just (subokL LΩ LM σ e₁ e₂ e₃ w wM d)
  go _ _ _ _ _ _ = nothing

-- θ : Ω → M is admissible for the rules over L when it is well typed
-- in the L core and certifies every marked variable of M.
record CertSubL (Ω : NCtx) (μΩ : List Name) (θ : Sub) (M : NCtx) (μM : List Name) : Set where
  constructor certsubL
  field
    typed : SubOKL Ω θ M
    certs : T (all (certAt μΩ M θ) μM)

------------------------------------------------------------------------
-- The P/L switch on the marking of cone-morphism shapes.

-- Comparison variables over the given diagram generators.
marksOver : NCtx → Name → List Name → List Name
marksOver Γ c = go
  where
  go : List Name → List Name
  go []       = []
  go (g ∷ gs) = mName Γ c g ∷ go gs

-- P: every positive-dimensional generator. (Agrees with morC's marks.)
marksP : NCtx → Name → Maybe (List Name)
marksP Γ c = morC Γ c >>= λ sh → just (Shape.marked sh)

-- L: only the marked generators μΓ.
marksL : NCtx → Name → (μΓ : List Name) → List Name
marksL Γ c μΓ = marksOver Γ c μΓ

------------------------------------------------------------------------
-- O1. The collapse instance is well typed in the L core.

O1 : SubOKL Ω θ Mfull
O1 = from-just (subL? Ω θ Mfull)

-- O2. Under L, f unmarked: nothing to certify.
O2-L : CertSubL Ω [] θ Mfull (marksL Γarr 3 [])
O2-L = certsubL O1 tt

-- O3. Under L, f (name 2) marked: m_f (12) must be certified.
_ : marksL Γarr 3 (2 ∷ []) ≡ (12 ∷ [])
_ = refl

O3-rejected : CertSubL Ω [] θ Mfull (marksL Γarr 3 (2 ∷ [])) → ⊥
O3-rejected (certsubL _ ())

O3-if-z-certified : CertSubL Ω (26 ∷ []) θ Mfull (marksL Γarr 3 (2 ∷ []))
O3-if-z-certified = certsubL O1 tt

-- Under P the marking is forced: m_f is marked.
_ : marksP Γarr 3 ≡ just (12 ∷ [])
_ = refl

------------------------------------------------------------------------
-- O4. The reverse interchanger cannot be formed as a coh in L, in any
-- context, for any substitution. (Only the coh is ruled out; see the
-- header for what is cited and what is open.)

O4 : ∀ {Γ σ B} → Γ L.⊢tm coh LEx.HComp LEx.ichTy⁻ σ ∶ B → ⊥
O4 = LEx.no-ich⁻
