------------------------------------------------------------------------
-- Every free variable is used by the closed support, in any pasting
-- context (S30, the ⇐ half of Lemma 4.2 of notes/lax-sc-completeness.md
-- §4, in several homs).
--
--   supp-fv⇐ : Γ ⊢ps → Γ ⊢tm t ∶ A → v ∈ FV(t) ∪ FV(A) →
--              v is not an object → usesVar v (↓supp(t : A))
--
-- for two-tier L whose coherence-case predicate cc forces equal closed
-- supports (CohSound, as for soundness) and Var-fullness of the source's
-- support (`VarFullHyp`); ccV of Gray.CohCaseVarSound satisfies both.
-- With the ⇒ half (Gray.G.SuppVars): over a pasting context the
-- variables used by ↓supp(t : A) are exactly the non-object variables
-- of t : A, i.e. Var(t : A) is the projected Gray support.
--
-- This generalises Strict.SuppFV (single hom, full-support rule). The
-- proof is the same induction on derivations; what changes:
--   * entries are tracked as members of tuples, not as singletons;
--   * for a coh c = coh_Δ(…)[σ] and a tuple s of the top support of
--     σ(g), a tuple τ_g = pre ++ g ∷ post of K(Δ) with 1-cells around g
--     is reached from the cell X of which c is the σ-image. In the
--     operation case τ_g is Gray.Through's tuple below the total cell;
--     in the coherence case X is the identity on t, and τ_g is obtained
--     from a tuple of ↓supp(t : A) through g (Var-fullness) by lowering
--     the other entries to 1-cells (Strict.PsSteps.through');
--   * F_σ(τ_g) contains Wp ++ s ++ Wq (1-cells have one top tuple), and
--     by Strict.LiftImage it lies in the face closure of supp(c);
--   * the closure is bounded: tuples of cells have degree ≤ dimK
--     (Strict.DegBound), so Gray paths from them have length ≤ dimK.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Pure using (∅)

module CaTTExp.Strict.G.SuppFV
  (cc : Signature.Ctx ∅ → Signature.Ty ∅ → List (List Nat) → List (List Nat) → Bool)
  where

open Signature ∅
open import CaTTExp.Gray.SupportG ∅ cc hiding (Tuple)
open import CaTTExp.TypingWith ∅ sideG
import CaTTExp.Subst ∅ sideG as S

open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.G.L cc
open import CaTTExp.Strict.G.Soundness cc
open import CaTTExp.Strict.G.Hyp cc using (flat-supp; closed; inv-gr)
open import CaTTExp.Strict.G.Subst cc using (applyF-cm)
open import CaTTExp.Strict.Cut using (∈L-++)
open import CaTTExp.Strict.Bridge using (T-cell)
open import CaTTExp.Strict.TopCell using (Pos; _⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Rad using (∈L-count)
open import CaTTExp.Strict.CohCase using (count-∈L; ∈L-++r; down-in; down-out; ≈T-r; rank-deg)
open import CaTTExp.Strict.Recon using (flat-sub; Sub-cell; topdeg; ∈L-++l)
open import CaTTExp.Strict.LiftImage using (image)
open import CaTTExp.Strict.SigmaFacts using (reach-obj)
open import CaTTExp.Strict.PsSteps using (objs-lookup; face-step; AllEnt; wft-ent; reach-ent; through'; reach-pre; reach-app)
open import CaTTExp.Strict.DegBound using (deg-wft)
import CaTTExp.Gray.Cover as C
open import CaTTExp.Gray.Cover using (Any; any-witness; _≤_; z≤n; s≤s; ≤-trans; ≤-refl; All-T)
  renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_; _∈ᴺ_; anyS⇒; anyS⇐; prodT⇐; upto⇐)
open import CaTTExp.Gray.DownAgree ∅ using (memT-sound; memT-complete; nub-complete) renaming (module Faces to DF)
import CaTTExp.Gray.Graded ∅ as Gr
open import CaTTExp.Gray.FullSupp ∅ using (InK; full-cover)
open import CaTTExp.Gray.PsFacts ∅ using (PsFacts; ps-facts)
open import CaTTExp.Gray.Through ∅
open import CaTTExp.Gray.G.SuppVars ∅ cc using (fv-ty[]; sc-fvTy)
open import CaTTExp.Gray.VarFull ∅ using (usesVar; isObj; varFull)

-- The hypothesis on cc used here besides CohSound.
VarFullHyp : Set
VarFullHyp = ∀ Θ A St Su → T (cc Θ A St Su) → T (varFull Θ St)

------------------------------------------------------------------------
-- Generalities.

private
  ⊎-elim : ∀ {A B R : Set} → A ⊎ B → (A → R) → (B → R) → R
  ⊎-elim (inj₁ a) f g = f a
  ⊎-elim (inj₂ b) f g = g b

  C⊎-elim : ∀ {A B R : Set} → A C.⊎ B → (A → R) → (B → R) → R
  C⊎-elim (C.inj₁ a) f g = f a
  C⊎-elim (C.inj₂ b) f g = g b

  lt-suc-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  lt-suc-ne zero    zero    _ ()
  lt-suc-ne zero    (suc n) _ _ = tt
  lt-suc-ne (suc i) (suc n) p q = lt-suc-ne i n p q

  lt-pred : ∀ i n → T (i <ℕ n) → T (i <ℕ suc (n ∸ 1))
  lt-pred i zero    ()
  lt-pred i (suc n) p = p

  le⇒≤ : ∀ a b → T (a <ℕ suc b) → a ≤ b
  le⇒≤ zero    b       _ = z≤n
  le⇒≤ (suc a) zero    ()
  le⇒≤ (suc a) (suc b) p = s≤s (le⇒≤ a b p)

  ∨-right : ∀ a {b} → (T a → ⊥) → T (a ∨ b) → T b
  ∨-right true  no p = ⊥-elim (no tt)
  ∨-right false no p = p

  ∈ᴺ-++l : ∀ {e} xs {ys} → e ∈ᴺ xs → e ∈ᴺ (xs ++ ys)
  ∈ᴺ-++l xs m = C.any-++l m

  ∈ᴺ-++r : ∀ {e} xs {ys} → e ∈ᴺ ys → e ∈ᴺ (xs ++ ys)
  ∈ᴺ-++r xs m = C.any-++r xs m

  ∈ᴺ-split : ∀ {g} xs → g ∈ᴺ xs → Σ Tuple λ p → Σ Tuple λ q → xs ≡ p ++ g ∷ q
  ∈ᴺ-split (x ∷ xs) (hereA refl) = [] , xs , refl
  ∈ᴺ-split (x ∷ xs) (thereA m) with ∈ᴺ-split xs m
  ... | p , q , e = x ∷ p , q , cong (x ∷_) e

  lookup-lt⁻ : ∀ Δ w → T (w <ℕ len Δ) → Σ Ty λ B → lookup Δ w ≡ just B
  lookup-lt⁻ (Δ ▸ A) w p with w ==ℕ len Δ in q
  ... | true  = A , refl
  ... | false = lookup-lt⁻ Δ w (lt-suc-ne w (len Δ) p q)

  lookₛ-new : ∀ σ t n → lenₛ σ ≡ n → lookupₛ (σ ,ₛ t) n ≡ t
  lookₛ-new σ t .(lenₛ σ) refl rewrite Gr.==-refl≡ (lenₛ σ) = refl

  lookₛ-old : ∀ σ t w → T (w <ℕ lenₛ σ) → lookupₛ (σ ,ₛ t) w ≡ lookupₛ σ w
  lookₛ-old σ t w p rewrite Gr.lt-ne w (lenₛ σ) p = refl

  -- A free variable of σ is a free variable of one of its terms.
  fvSub-dom : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → ∀ {v} → v ∈ᴺ fvSub σ →
              Σ Nat λ w → Σ Ty λ B → (lookup Δ w ≡ just B) × (v ∈ᴺ fvTm (lookupₛ σ w))
  fvSub-dom (⟨⟩-wf _) ()
  fvSub-dom (,-wf {σ} {Δ} {t} {A} sσ d) {v} m with S.sub-sc closed sσ | C.any-++⁻ (fvSub σ) m
  ... | (_ , l) | C.inj₂ b = len Δ , A , lookup-new Δ A , subst (λ X → v ∈ᴺ fvTm X) (sym (lookₛ-new σ t (len Δ) l)) b
  ... | (_ , l) | C.inj₁ a with fvSub-dom sσ a
  ...   | w , B , lw , mv =
    w , B , lookup-ext Δ A w lw ,
    subst (λ X → v ∈ᴺ fvTm X) (sym (lookₛ-old σ t w (subst (λ n → T (w <ℕ n)) (sym l) (lookup-lt Δ w lw)))) mv

  -- The supports in a substituted variable tower are top supports of
  -- σ's terms.
  suppTy-sub : ∀ {Δ σ} → PsInv Δ → ∀ B → VarTower Δ B → ∀ {s} → s ∈L suppTy (B [ σ ]ty) →
               Σ Nat λ g → Σ Ty λ Cg → (lookup Δ g ≡ just Cg) × (s ∈L topS (lookupₛ σ g))
  suppTy-sub inv ⋆ _ ()
  suppTy-sub inv (arr ⋆ _ _) _ ()
  suppTy-sub {σ = σ} inv (arr (arr B a b) s u) (i , j , es , eu , li , lj) {s'} m =
    ⊎-elim (∈L-++ (suppTy (arr B a b [ σ ]ty)) m)
      (λ x → suppTy-sub inv (arr B a b) (inv i _ li) x)
      (λ y → ⊎-elim (∈L-++ (topS (s [ σ ]tm)) y)
        (λ z → i , _ , li , subst (λ X → s' ∈L topS (X [ σ ]tm)) es z)
        (λ z → j , _ , lj , subst (λ X → s' ∈L topS (X [ σ ]tm)) eu z))

  flat-≈w : ∀ X Y → X ≈w Y → flat X ≈ flat Y
  flat-≈w (base c)     (base c')       p           = p
  flat-≈w (step S U c) (step S' U' c') (p , q , r) = ++-cong (flat-≈w S S' p) (++-cong (flat-≈w U U' q) r)

  mem≈ : ∀ {X Y z} → X ≈ Y → z ∈L X → z ∈L Y
  mem≈ {X} {Y} {z} p m = count-∈L z Y (subst Pos (at p z) (∈L-count z X m))

  psf : ∀ {Δ} → Δ ⊢ps → PsFacts Δ
  psf (ps d) = fst (ps-facts d)

  -- Tuples of a cell are composable.
  cell-wft : ∀ {Δ} → Δ ⊢ps → ∀ {x y n X} → IsCellL Δ x y n X → ∀ {s} → s ∈L flat X →
             Σ Nat λ a → Σ Nat λ b → WFT Δ a b s
  cell-wft P {x} {y} {n} {X} cX ms with flat-sub P n X cX ms
  ... | m , V , sub , mv = x , y , fst (topdeg P m V (Sub-cell P cX sub) mv)

  -- Membership in the support of a term of arrow type is membership in
  -- its tower.
  supp-flat : ∀ t B p q {s} → s ∈L supp t (arr B p q) → s ∈L flat (towerOf t (arr B p q))
  supp-flat t B p q {s} ms = memT-sound s _ (subst T (sym (flat-supp t B p q s)) (memT-complete s _ ms))

  flat-supp' : ∀ t B p q {s} → s ∈L flat (towerOf t (arr B p q)) → s ∈L supp t (arr B p q)
  flat-supp' t B p q {s} ms = memT-sound s _ (subst T (flat-supp t B p q s) (memT-complete s _ ms))

------------------------------------------------------------------------
-- The theorem, over a pasting context Γ.

module _ (hcc : CohSound) (hvf : VarFullHyp) {Γ : Ctx} (PΓ : Γ ⊢ps) where

  open Soundness hcc using (sound-tm; sound-sub; cohX; cohX-cell; cohX-image)

  private
    invΓ = psInv PΓ
    PFΓ  = psf PΓ
    module F = DF (cells Γ)
    N = dimK (homs Γ)

  NonObj : Nat → Set
  NonObj v = lookup Γ v ≡ just ⋆ → ⊥

  -- Tuples reached from supp(t : A) by Gray steps.
  Cl : Tm → Ty → Tuple → Set
  Cl t A z = Σ Tuple λ s → (s ∈L supp t A) × Σ Nat λ k → F.Reach k s z

  -- Every non-object variable of t : A is an entry of such a tuple.
  Q : Tm → Ty → Set
  Q t A = ∀ {v} → v ∈ᴺ fvTmTy t A → NonObj v → Σ Tuple λ z → Cl t A z × (v ∈ᴺ z)

  private
    Cl-face : ∀ {t A z z'} → Cl t A z → z' ∈L ∂T Γ true z → Cl t A z'
    Cl-face (s , ms , k , r) m = s , ms , k + 1 , F.reach-++ r (F.step (face-step Γ PFΓ true m) F.done)

    Cl-reach : ∀ {t A z z' k} → Cl t A z → F.Reach k z z' → Cl t A z'
    Cl-reach (s , ms , j , r) r' = s , ms , _ , F.reach-++ r r'

  ----------------------------------------------------------------------
  -- The core: σ-images of tuples through a variable g of Δ, with
  -- 1-cells elsewhere, are in the closure.

  module Core {Δ σ x y x' y' n X} (psΔ : Δ ⊢ps) (cellσ : Cellular Γ σ Δ) (lenσ : lenₛ σ ≡ len Δ)
    (σx : lookupₛ σ x ≡ var x') (σy : lookupₛ σ y ≡ var y') (cX : IsCellL Δ x y n X)
    (Cl' : Tuple → Set) (Cl'-face : ∀ {z z'} → Cl' z → z' ∈L ∂T Γ true z → Cl' z')
    (good : ∀ {z} → z ∈L flat (mapTw (cm (Ftuple (topsSub σ))) X) → Cl' z)
    where

    private
      module SM = SubstMap cellσ lenσ (psInv psΔ)
      module Tr = Transport (∂T Δ) (Basis Δ x y) (∂T Γ) (Basis Γ x' y') SM.Fσ
                    (λ k w bw → SM.F-basis k w x y x' y' σx σy bw)
                    (λ w bw → SM.F-aug w x y bw)
                    (λ k w b bw → SM.F-chain k w x y x' b σx bw)
      PF = psf psΔ

      -- The top support of a 1-cell is a single tuple.
      sel : ∀ o Co → dim Co ≡ 1 → IsCellTm Γ (lookupₛ σ o) (Co [ σ ]ty) → Σ Tuple λ w → w ∈L topS (lookupₛ σ o)
      sel o ⋆ ()
      sel o (arr (arr _ _ _) _ _) ()
      sel o (arr ⋆ p q) _ (_ , _ , _ , _ , (w , pw , _)) =
        w , count-∈L w _ (subst Pos (sym (at pw w)) (∈L-count w (w ∷ []) (hereA refl)))

      oneTop : ∀ o → One Δ PF o → Σ Tuple λ w → w ∈L nth o SM.Sσ
      oneTop o (Co , lo , d1) with sel o Co d1 (cellσ o Co lo)
      ... | w , mw = w , subst (w ∈L_) (sym (SM.nthσ o lo)) mw

      pre-mem : ∀ pre → AllOne Δ PF pre → ∀ rest {z} → z ∈L SM.Fσ rest →
                Σ Tuple λ W → (W ++ z) ∈L SM.Fσ (pre ++ rest)
      pre-mem []        []        rest m = [] , m
      pre-mem (o ∷ pre) (oo ∷ ap) rest {z} m with oneTop o oo | pre-mem pre ap rest m
      ... | w , mw | W , mW =
        w ++ W ,
        subst (_∈L SM.Fσ (o ∷ (pre ++ rest))) (sym (++-assocL w W z))
          (prodT⇐ (nth o SM.Sσ) (SM.Fσ (pre ++ rest)) mw mW)

      post-mem : ∀ post → AllOne Δ PF post → Σ Tuple λ W → W ∈L SM.Fσ post
      post-mem []         []        = [] , hereA refl
      post-mem (o ∷ post) (oo ∷ ap) with oneTop o oo | post-mem post ap
      ... | w , mw | W , mW = w ++ W , prodT⇐ (nth o SM.Sσ) (SM.Fσ post) mw mW

    hit : ∀ g Cg → lookup Δ g ≡ just Cg → ∀ pre post → AllOne Δ PF pre → AllOne Δ PF post →
          (Σ Tuple λ s → (s ∈L flat X) × Σ Nat λ j → DF.Reach (cells Δ) j s (pre ++ g ∷ post)) →
          ∀ s' → s' ∈L topS (lookupₛ σ g) → Σ Tuple λ Wp → Σ Tuple λ Wq → Cl' (Wp ++ s' ++ Wq)
    hit g Cg lg pre post ap aq cov s' ms' with post-mem post aq
    ... | Wq , mWq
      with pre-mem pre ap (g ∷ post) {s' ++ Wq}
             (prodT⇐ (nth g SM.Sσ) (SM.Fσ post) (subst (s' ∈L_) (sym (SM.nthσ g lg)) ms') mWq)
    ...   | Wp , mW = Wp , Wq , image psΔ {x} {y} SM.Fσ Tr.f-chain Cl' Cl'-face cX good cov mW

  ----------------------------------------------------------------------
  -- Below the total cell (operation case).

  private
    fc : ∀ {Δ τ} → InK Δ (homs Δ) τ →
         Σ Tuple λ f → (f ∈L fullT (homs Δ)) × Σ Nat λ k → DF.Reach (cells Δ) k f τ
    fc {Δ} {τ} kτ with any-witness (anyS⇒ (leqT (cells Δ) (dimK (homs Δ)) τ) (fullT (homs Δ)) (full-cover Δ kτ))
    ... | f , mf , q with DF.pw⇒reach (cells Δ) (DF.leqT⇒ (cells Δ) (dimK (homs Δ)) τ f q)
    ...   | k , r = f , mf , k , r

    -- A variable g of Δ (not an object) used by a Var-full support S
    -- is an entry of a tuple of ↓S.
    not-obj : ∀ Δ g Cg → lookup Δ g ≡ just Cg → isStar Cg ≡ false → T (isObj Δ g) → ⊥
    not-obj Δ g Cg lg st o with any-witness (anyS⇒ (λ j → g ==ℕ j) (objs Δ) o)
    ... | j , mj , e with ==ℕ-sound g j e
    ...   | refl with trans (sym lg) (objs-lookup Δ mj)
    ...     | refl with st
    ...       | ()

    vf-use : ∀ {Δ S} g Cg → lookup Δ g ≡ just Cg → isStar Cg ≡ false → T (varFull Δ S) →
             Σ Tuple λ τ → (τ ∈L down Δ S) × (g ∈ᴺ τ)
    vf-use {Δ} {S} g Cg lg st vf
      with any-witness (anyS⇒ _ (down Δ S)
             (∨-right (isObj Δ g) (not-obj Δ g Cg lg st)
               (All-T (λ i → isObj Δ i ∨ usesVar i (down Δ S)) (upto (len Δ ∸ 1)) vf
                 (upto⇐ g (len Δ ∸ 1) (lt-pred g (len Δ) (lookup-lt Δ g lg))))))
    ... | τ , mτ , u with any-witness (anyS⇒ (λ j → g ==ℕ j) τ u)
    ...   | j , mj , e with ==ℕ-sound g j e
    ...     | refl = τ , mτ , mj

    -- Every derivable coh hits the variables of Δ through σ.
    hitC : ∀ {Δ A t u σ} → Δ ⊢ps → Δ ⊢ctx → (tyΔ : Δ ⊢ty arr A t u) → (ok : T (sideG Δ A t u)) →
           (sσ : Γ ⊢sub σ ∶ Δ) → ∀ g Cg → lookup Δ g ≡ just Cg → isStar Cg ≡ false →
           ∀ s' → s' ∈L topS (lookupₛ σ g) →
           Σ Tuple λ Wp → Σ Tuple λ Wq → Cl (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty) (Wp ++ s' ++ Wq)
    hitC {Δ} {⋆} {t} {u} {σ} psΔ ctxΔ tyΔ@(arr-wf d e) ok sσ g Cg lg st s' ms'
      with sound-tm (psInv psΔ) d | sound-tm (psInv psΔ) e
    ... | (i , refl , li) | (j , refl , lj) with through Δ (psf psΔ) g Cg lg st
    ...   | pre , post , kτ , ap , aq =
      Core.hit {n = dimK hs} {X = twT hs true (dimK hs)} psΔ cellσ lenσ σi σj cT (Cl c A')
        (λ {z} {z'} → Cl-face {c} {A'} {z} {z'}) good g Cg lg pre post ap aq (cover kτ) s' ms'
      where
      c  = coh Δ (arr ⋆ (var i) (var j)) σ
      A' = arr ⋆ (var i) (var j) [ σ ]ty
      hs = homs Δ
      cellσ = sound-sub invΓ ctxΔ sσ
      lenσ = snd (S.sub-sc closed sσ)
      σi = fst (snd (cellσ i ⋆ li))
      σj = fst (snd (cellσ j ⋆ lj))
      d0 : dimK hs ≡ 0
      okC : T (opCaseC Δ ⋆ (var i) (var j))
      okC = ∨-right (cohG Δ ⋆ (var i) (var j)) (λ ()) ok
      d0 = ==ℕ-sound (dimK hs) 0 (∧-fst okC)
      cT = T-cell psΔ (arr ⋆ (var i) (var j)) i j (∧-snd {dimK hs ==ℕ 0} okC) refl
      g0 : ∀ (h : Bag → Bag) m {z} → m ≡ 0 → z ∈L flat (mapTw h (twT hs true m)) → z ∈L h (chainT true m hs)
      g0 h .0 refl mz = mz
      good : ∀ {z} → z ∈L flat (mapTw (cm (Ftuple (topsSub σ))) (twT hs true (dimK hs))) → Cl c A' z
      good {z} mz =
        z , ∈L-++l (topS c) _ (subst (z ∈L_) (sym (applyF-cm (topsSub σ) (topT hs))) (g0 _ (dimK hs) d0 mz)) , 0 , F.done
      cover : ∀ {τ} → InK Δ hs τ → Σ Tuple λ s → (s ∈L flat (twT hs true (dimK hs))) × Σ Nat λ j → DF.Reach (cells Δ) j s τ
      cover kτ with fc kτ
      ... | f , mf , k , r =
        f , memT-sound f _ (subst T (sym (flat-twT hs true (dimK hs) f)) (memT-complete f (fullT hs) mf)) , k , r
    hitC {Δ} {arr A₀ a₀ b₀} {t} {u} {σ} psΔ ctxΔ tyΔ@(arr-wf d e) ok sσ g Cg lg st s' ms'
      with sound-tm (psInv psΔ) d | sound-tm (psInv psΔ) e
    ... | ((e₁ , e₂) , ee , l₁ , l₂ , cT) | ((e₁' , e₂') , ee' , _ , _ , cU') =
      let (pre , post , ap , aq , cvr) = cov (cohG Δ A t u) refl in
      Core.hit {n = dim A} {X = X} psΔ cellσ lenσ σx σy cX (Cl c A')
        (λ {z} {z'} → Cl-face {c} {A'} {z} {z'}) good g Cg lg pre post ap aq cvr s' ms'
      where
      A  = arr A₀ a₀ b₀
      c  = coh Δ (arr A t u) σ
      A' = arr A t u [ σ ]ty
      hs = homs Δ
      Sσ = topsSub σ
      PF = psf psΔ
      cellσ = sound-sub invΓ ctxΔ sσ
      lenσ = snd (S.sub-sc closed sσ)
      σx = fst (snd (cellσ e₁ ⋆ l₁))
      σy = fst (snd (cellσ e₂ ⋆ l₂))
      cU : IsCellL Δ e₁ e₂ (dim A₀) (towerOf u A)
      cU = subst (λ e' → IsCellL Δ (fst e') (snd e') (dim A₀) (towerOf u A)) (just-inj (trans (sym ee') ee)) cU'
      cX = cohX-cell A₀ a₀ b₀ psΔ ok e₁ e₂ ee cT cU
      X = cohX Δ A t u

      good : ∀ {z} → z ∈L flat (mapTw (cm (Ftuple Sσ)) X) → Cl c A' z
      good {z} mz =
        let m₁ = subst (λ W → z ∈L flat W) (sym (mapTw-ext (applyF Sσ) (cm (Ftuple Sσ)) (applyF-cm Sσ) X)) mz
            m₂ = mem≈ (flat-≈w _ _ (cohX-image A₀ a₀ b₀ sσ d e)) m₁
            m₃ = memT-sound z _ (subst T (flat-supp c (A [ σ ]ty) (t [ σ ]tm) (u [ σ ]tm) z) (memT-complete z _ m₂))
        in z , m₃ , 0 , F.done

      -- A tuple of the closed support of t (or u) is in that of X.
      fromT : ∀ {top} R → T (≈T (down Δ (supp t A)) (down Δ R)) → ∀ {f} → f ∈L R →
              Σ Tuple λ s → (s ∈L flat (step (towerOf t A) (towerOf u A) top)) × Σ Nat λ j → DF.Reach (cells Δ) j s f
      fromT R p {f} mf with down-out psΔ (supp t A) (≈T-r psΔ (down Δ (supp t A)) (down Δ R) {f} p (down-in psΔ R mf))
      ... | s , ms , j , r = s , ∈L-++l (flat (towerOf t A)) _ (supp-flat t A₀ a₀ b₀ ms) , j , r

      fromU : ∀ {top} R → T (≈T (down Δ (supp u A)) (down Δ R)) → ∀ {f} → f ∈L R →
              Σ Tuple λ s → (s ∈L flat (step (towerOf t A) (towerOf u A) top)) × Σ Nat λ j → DF.Reach (cells Δ) j s f
      fromU R p {f} mf with down-out psΔ (supp u A) (≈T-r psΔ (down Δ (supp u A)) (down Δ R) {f} p (down-in psΔ R mf))
      ... | s , ms , j , r =
        s , ∈L-++r (flat (towerOf t A)) (∈L-++l (flat (towerOf u A)) _ (supp-flat u A₀ a₀ b₀ ms)) , j , r

      opsplit : ∀ m → suc (dim A₀) ≡ m → ∀ {f} → f ∈L (lowerT m hs ++ chainT true m hs) →
                T (≈T (down Δ (supp t A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT false (m ∸ 1) hs))) →
                T (≈T (down Δ (supp u A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT true (m ∸ 1) hs))) →
                Σ Tuple λ s → (s ∈L flat (step (towerOf t A) (towerOf u A) (chainT true m hs))) ×
                Σ Nat λ j → DF.Reach (cells Δ) j s f
      opsplit .(suc (dim A₀)) refl {f} mf pt pu with ∈L-++ (lowerT (suc (dim A₀)) hs) mf
      ... | inj₂ mtop = f , ∈L-++r (flat (towerOf t A)) (∈L-++r (flat (towerOf u A)) mtop) , 0 , DF.done
      ... | inj₁ ml with ∈L-++ (lowerT (dim A₀) hs) ml
      ...   | inj₁ a = fromT _ pt (∈L-++l (lowerT (dim A₀) hs) _ a)
      ...   | inj₂ b with ∈L-++ (chainT false (dim A₀) hs) b
      ...     | inj₁ c' = fromT _ pt (∈L-++r (lowerT (dim A₀) hs) c')
      ...     | inj₂ d' = fromU _ pu (∈L-++r (lowerT (dim A₀) hs) d')

      Cov : Bool → Set
      Cov b = Σ Tuple λ pre → Σ Tuple λ post → AllOne Δ PF pre × AllOne Δ PF post ×
              (Σ Tuple λ s → (s ∈L flat (step (towerOf t A) (towerOf u A) (if b then [] else topT hs))) ×
               Σ Nat λ j → DF.Reach (cells Δ) j s (pre ++ g ∷ post))

      -- coherence case: through a tuple of ↓supp(t : A) using g
      covC : T (varFull Δ (supp t A)) → Cov true
      covC vf with vf-use {Δ} {supp t A} g Cg lg st vf
      ... | τ , mτ , mg with down-out psΔ (supp t A) {τ} (memT-complete τ _ mτ)
      ...   | s , ms , j , r with ∈ᴺ-split τ mg
      ...     | p , q , refl with cell-wft psΔ cT (supp-flat t A₀ a₀ b₀ ms)
      ...       | _ , _ , ws with through' Δ PF p g q (reach-ent Δ PF r (wft-ent Δ PF s ws))
      ...         | pre , post , ap , aq , k , r' =
        pre , post , ap , aq , s , ∈L-++l (flat (towerOf t A)) _ (supp-flat t A₀ a₀ b₀ ms) , j + k ,
        DF.reach-++ (cells Δ) r r'

      -- operation case: Gray.Through's tuple, below the total cell
      covO' : suc (dim A₀) ≡ dimK hs →
              T (≈T (down Δ (supp t A)) (down Δ (lowerT (dimK hs ∸ 1) hs ++ chainT false (dimK hs ∸ 1) hs))) →
              T (≈T (down Δ (supp u A)) (down Δ (lowerT (dimK hs ∸ 1) hs ++ chainT true (dimK hs ∸ 1) hs))) →
              Cov false
      covO' dA pt pu with through Δ PF g Cg lg st
      ... | pre , post , kτ , ap , aq with fc kτ
      ...   | f , mf , k , r with opsplit (dimK hs) dA mf pt pu
      ...     | s , ms , j , r' = pre , post , ap , aq , s , ms , j + k , DF.reach-++ (cells Δ) r' r

      covO : T (opCaseC Δ A t u) → Cov false
      covO oc = covO' dA (∧-fst rest) (∧-snd {sameDownClosure Δ (supp t A) (bdryT false hs)} rest)
        where
        dA   = ==ℕ-sound (dim A) (dimK hs) (∧-fst (∧-snd {endsOK Δ A} oc))
        rest = ∧-snd {dim A ==ℕ dimK hs} (∧-snd {endsOK Δ A} oc)

      cov : ∀ b → cohG Δ A t u ≡ b → Cov b
      cov true  ec = covC (hvf Δ A (supp t A) (supp u A) (subst T (sym ec) tt))
      cov false ec = covO (∨-right (cohG Δ A t u) (λ x → subst T ec x) ok)

  ----------------------------------------------------------------------
  -- Induction on derivations.

  private
    tyQ : ∀ A → VarTower Γ A → ∀ {v} → v ∈ᴺ fvTy A → NonObj v → (v ∷ []) ∈L suppTy A
    tyQ ⋆ _ ()
    tyQ (arr ⋆ s u) (i , j , refl , refl , li , lj) (hereA refl) no = ⊥-elim (no li)
    tyQ (arr ⋆ s u) (i , j , refl , refl , li , lj) (thereA (hereA refl)) no = ⊥-elim (no lj)
    tyQ (arr ⋆ s u) (i , j , refl , refl , li , lj) (thereA (thereA ())) no
    tyQ (arr (arr B a b) s u) (i , j , refl , refl , li , lj) {v} m no =
      C⊎-elim (C.any-++⁻ (fvTy (arr B a b)) m)
        (λ x → ∈L-++l (suppTy (arr B a b)) _ (tyQ (arr B a b) (invΓ i _ li) x no))
        (λ y → ∈L-++r (suppTy (arr B a b)) (two y))
      where
      two : v ∈ᴺ (i ∷ j ∷ []) → (v ∷ []) ∈L ((i ∷ []) ∷ (j ∷ []) ∷ [])
      two (hereA refl) = hereA refl
      two (thereA (hereA refl)) = thereA (hereA refl)
      two (thereA (thereA ()))

    Qvar : ∀ {w A} → lookup Γ w ≡ just A → Q (var w) A
    Qvar {w} lw (hereA refl) no = (w ∷ []) , ((w ∷ []) , hereA refl , 0 , F.done) , hereA refl
    Qvar {w} {A} lw {v} (thereA m) no =
      (v ∷ []) , ((v ∷ []) , thereA (tyQ A (invΓ w A lw) m no) , 0 , F.done) , hereA refl

    dom : ∀ {Δ A t u σ} → Δ ⊢ty arr A t u → Γ ⊢sub σ ∶ Δ → ∀ {v} →
          v ∈ᴺ fvTmTy (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty) →
          Σ Nat λ w → Σ Ty λ B → (lookup Δ w ≡ just B) × (v ∈ᴺ fvTm (lookupₛ σ w))
    dom {Δ} {A} {t} {u} {σ} tyΔ sσ m' with C.any-++⁻ (fvSub σ) m'
    ... | C.inj₁ a = fvSub-dom sσ a
    ... | C.inj₂ b with fv-ty[] (arr A t u) σ b
    ...   | w , mw , mv with lookup-lt⁻ Δ w (sc-fvTy (len Δ) (arr A t u) (S.ty-sc closed tyΔ) mw)
    ...     | B , lw = w , B , lw , mv

    tops : ∀ {Δ σ w B s} → PsInv Δ → lookup Δ w ≡ just B →
           (s ∈L topS (lookupₛ σ w)) ⊎ (s ∈L suppTy (B [ σ ]ty)) →
           Σ Nat λ g → Σ Ty λ Cg → (lookup Δ g ≡ just Cg) × (s ∈L topS (lookupₛ σ g))
    tops {w = w} {B} inv lw (inj₁ x) = w , B , lw , x
    tops {w = w} {B} inv lw (inj₂ y) = suppTy-sub inv B (inv w B lw) y

    byStar : ∀ {Δ A t u σ} → (psΔ : Δ ⊢ps) (ctxΔ : Δ ⊢ctx) (tyΔ : Δ ⊢ty arr A t u) (ok : T (sideG Δ A t u)) →
             (sσ : Γ ⊢sub σ ∶ Δ) → ∀ {v} → NonObj v → ∀ {s z k} → F.Reach k s z → v ∈ᴺ z →
             ∀ g Cg → lookup Δ g ≡ just Cg → s ∈L topS (lookupₛ σ g) →
             Σ Tuple λ z' → Cl (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty) z' × (v ∈ᴺ z')
    byStar psΔ ctxΔ tyΔ ok sσ {v} no {s} r mv g ⋆ lg mg with sound-sub invΓ ctxΔ sσ g ⋆ lg
    ... | i , eq , li with subst (λ X → s ∈L topS X) eq mg
    ...   | thereA ()
    ...   | hereA refl with reach-obj Γ i li r
    ...     | refl with mv
    ...       | hereA refl = ⊥-elim (no li)
    ...       | thereA ()
    byStar {Δ} {A} {t} {u} {σ} psΔ ctxΔ tyΔ ok sσ {v} no {s} {z} r mv g Cg@(arr _ _ _) lg mg
      with hitC psΔ ctxΔ tyΔ ok sσ g Cg lg refl s mg
    ... | Wp , Wq , cW =
      Wp ++ z ++ Wq ,
      Cl-reach {coh Δ (arr A t u) σ} {arr A t u [ σ ]ty} cW (reach-pre Γ PFΓ Wp (reach-app Γ PFΓ Wq r)) ,
      ∈ᴺ-++r Wp (∈ᴺ-++l z mv)

    Qcoh : ∀ {Δ A t u σ} → (psΔ : Δ ⊢ps) (ctxΔ : Δ ⊢ctx) (tyΔ : Δ ⊢ty arr A t u) (ok : T (sideG Δ A t u)) →
           (sσ : Γ ⊢sub σ ∶ Δ) → (∀ w B → lookup Δ w ≡ just B → Q (lookupₛ σ w) (B [ σ ]ty)) →
           Q (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
    Qcoh {Δ} {A} {t} {u} {σ} psΔ ctxΔ tyΔ ok sσ IH {v} m no with dom tyΔ sσ m
    ... | w , B , lw , mv with IH w B lw (C.any-++l mv) no
    ...   | z , (s , ms , k , r) , mz with tops {σ = σ} (psInv psΔ) lw (∈L-++ (topS (lookupₛ σ w)) ms)
    ...     | g , Cg , lg , mg = byStar psΔ ctxΔ tyΔ ok sσ no r mz g Cg lg mg

  mutual
    Qtm : ∀ {t A} → Γ ⊢tm t ∶ A → Q t A
    Qtm (var-wf _ eq) = Qvar eq
    Qtm (coh-wf psΔ ctxΔ tyΔ ok sσ) = Qcoh psΔ ctxΔ tyΔ ok sσ (Qsub ctxΔ sσ)
    Qtm (cst-wf {()} _ _)

    Qsub : ∀ {σ Δ} → Δ ⊢ctx → Γ ⊢sub σ ∶ Δ → ∀ v B → lookup Δ v ≡ just B → Q (lookupₛ σ v) (B [ σ ]ty)
    Qsub ε-wf (⟨⟩-wf _) v B ()
    Qsub (▸-wf {Δ} {A} w a) (,-wf {σ} {_} {t} sσ d) v B eq with S.sub-sc closed sσ
    ... | (_ , l) with v ==ℕ len Δ in e
    ...   | true rewrite l | e =
      subst (λ X → Q t (X [ σ ,ₛ t ]ty)) (just-inj eq)
        (subst (Q t) (sym (S.ext-ty A σ t (subst (λ n → S.ScTy n A) (sym l) (S.ty-sc closed a)))) (Qtm d))
    ...   | false rewrite l | e =
      subst (Q (lookupₛ σ v))
        (sym (S.ext-ty B σ t (subst (λ n → S.ScTy n B) (sym l) (snd (S.ctx-lookup closed w eq)))))
        (Qsub w sσ v B eq)

  ----------------------------------------------------------------------
  -- The theorem.

  private
    -- Tuples of supports of derivable terms have rank ≤ dimK.
    supp-rank : ∀ {t B p q} → Γ ⊢tm t ∶ arr B p q → ∀ {s} → s ∈L supp t (arr B p q) → F.rank s ≤ N
    supp-rank {t} {B} {p} {q} d {s} ms with sound-tm invΓ d
    ... | _ , _ , _ , _ , cX with cell-wft PΓ cX (supp-flat t B p q ms)
    ...   | a , b , ws = subst (_≤ N) (sym (rank-deg PΓ a b s ws)) (le⇒≤ (deg Γ s) N (deg-wft PΓ a b s ws))

    usesVar⇐ : ∀ v S {z} → z ∈L S → v ∈ᴺ z → T (usesVar v S)
    usesVar⇐ v S {z} mz mv =
      anyS⇐ _ S (C.any-mono (λ { refl → anyS⇐ (λ j → v ==ℕ j) z (C.any-mono (λ { refl → ==ℕ-refl v }) mv) }) mz)

  supp-fv⇐ : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ {v} → v ∈ᴺ fvTmTy t A → NonObj v →
             T (usesVar v (down Γ (supp t A)))
  supp-fv⇐ {t} {⋆} d m no with sound-tm invΓ d
  ... | i , refl , li with m
  ...   | hereA refl = ⊥-elim (no li)
  ...   | thereA ()
  supp-fv⇐ {t} {A@(arr B p q)} d {v} m no with Qtm d m no
  ... | z , (s , ms , k , r) , mz =
    usesVar⇐ v _ (F.close⇐ N (nubT (supp t A)) (s , nub-complete (supp t A) ms , k , bound , r)) mz
    where
    G = Gr.graded Γ (inv-gr invΓ)
    bound : k ≤ N
    bound = F.reach-bound G r (supp-rank d ms)
