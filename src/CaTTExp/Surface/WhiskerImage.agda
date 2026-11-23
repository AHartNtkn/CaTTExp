------------------------------------------------------------------------
-- Theorem B's unit law Wh-≈ for image equality, generic in the strict
-- model.
--
-- Setting: the whiskering interface of CaTTExp.Surface.WhiskerWith
-- (any side condition accepting the derived whisker heads), and a
-- strict model presented by the top chain `cohT` of a coherence (see
-- CaTTExp.Surface.Image). The surface equality is the one generated
-- (CaTTExp.Surface.Generated) by
--
--   Base Γ t u  =  t, u well typed over Γ and ⟦t⟧(η Γ) ≈w ⟦u⟧(η Γ),
--
-- i.e. by equality of images in the strict model at the generic
-- environment of Γ (image equality ≡_F of the note, on typed terms),
-- and "≈ an identity" is `Unit Γ p = UnitTw ⟦p⟧(η Γ)`: the image of p
-- is an identity cell of the model.
--
-- The hypotheses on the model are exactly strict unitality for the
-- four whisker heads: the top chain of the head is the top chain of
-- the whiskered cell when the whiskering cell's image is an identity
-- (`HR0`, `HR`, `HL0`, `HL`), and an identity has equal source and
-- target (`unit-par`). From them:
--
--   headR, headL : the image of a whisker head, applied in any
--                  environment with the right boundaries whose
--                  whiskering cell is an identity, is the image of the
--                  whiskered cell (by induction on the codimension);
--   Wh-≈         : TheoremB's unit law, Γ ∣ (p ◃ₖ x) ▹ₖ q ≈ x when the
--                  images of p and q are identities.
--
-- `module Instance` then instantiates TheoremB.Hyp and Thm with every
-- hypothesis discharged (inv-arr and dim-≈ from Generated, presup from
-- the kernel, Wh-wf from WhiskerWith), so `kc-from-el` holds for this
-- ≈ with no open module parameter. (`conservative-from-el` still takes
-- (SC), `SideResp`, as an argument.)
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Signature
open Signature ∅
import CaTTExp.Subst as SubstM
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.Derived using (nB; zK; BK; wK; LK; LPK; lK; ρK; ρsK; ρtK; λsK; λtK; tL; bLK; hTy)
open import CaTTExp.Strict.Bag using (Bag; _≈_; ≈-refl; ≈-sym; ≈-trans; ≡→≈)
open import CaTTExp.Strict.Cell using (Tower; base; step; top; _≈w_; ≈w-refl; ≈w-sym; ≈w-trans)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (Env; []ₑ; _,ₑ_; lenₑ; lookupₑ)

module CaTTExp.Surface.WhiskerImage
  (side : Ctx → Ty → Tm → Tm → Bool)
  (closedS : SubstM.Closed ∅ side)
  (side-BK0 : ∀ k → T (side (BK k 0) (aL k) (var (dbl k)) (var (zK k 0))))
  (side-BK  : ∀ k j → T (side (BK k (suc j)) (wK k j [ ρsK k j ]ty)
                         (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j))))
  (side-LK  : ∀ k j → T (side (LK k (suc j)) (lK k j [ λsK k j ]ty)
                         (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j))))
  (cohT : Ctx → Ty → Tm → Tm → Env → Bag)
  (UnitTw : Tower → Set)
  (unit-par : ∀ S U c → UnitTw (step S U c) → S ≈w U)
  (HR0 : ∀ k ρ → UnitTw (lookupₑ ρ (suc (zK k 0))) →
         cohT (BK k 0) (aL k) (var (dbl k)) (var (zK k 0)) ρ ≈ top (lookupₑ ρ (dbl (nB k 0))))
  (HR  : ∀ k j ρ → UnitTw (lookupₑ ρ (suc (zK k (suc j)))) →
         cohT (BK k (suc j)) (wK k j [ ρsK k j ]ty)
              (coh (BK k j) (wK k j) (ρsK k j)) (coh (BK k j) (wK k j) (ρtK k j)) ρ
           ≈ top (lookupₑ ρ (dbl (nB k (suc j)))))
  (HL0 : ∀ k ρ → UnitTw (lookupₑ ρ (dbl (suc k))) →
         cohT (LK k 0) (aL k) (var (dbl k)) (var (zK k 0)) ρ ≈ top (lookupₑ ρ (tL k 0)))
  (HL  : ∀ k j ρ → UnitTw (lookupₑ ρ (dbl (suc k))) →
         cohT (LK k (suc j)) (lK k j [ λsK k j ]ty)
              (coh (LK k j) (lK k j) (λsK k j)) (coh (LK k j) (lK k j) (λtK k j)) ρ
           ≈ top (lookupₑ ρ (tL k (suc j))))
  where

open import CaTTExp.TypingWith ∅ side
import CaTTExp.Subst ∅ side as Sg
import CaTTExp.Derived as D
open import CaTTExp.GrayCtx.NaturalWF using (dim-aL; <-suc; n<sn)
open import CaTTExp.DerivedBoundary
  using (σR; rwT; tyK; tgtK; srcK; hL; σLp; σL; lwT; lenₛ-σLp; dim-tyK)
open import CaTTExp.DerivedWith side closedS side-BK0 side-BK side-LK
  using (tm-ty; σR-wf; σL-wf; lwT-wf; wBK; wLK; ρK-wf; λsK-wf; λtK-wf)
open import CaTTExp.Surface.Image side closedS cohT
open import CaTTExp.Surface.TheoremB ∅ side closedS using (Pre; here; there; module Hyp)
open import CaTTExp.Surface.WhiskerWith side closedS side-BK0 side-BK side-LK
  using (wh; rawW; tyOf-ok; depth; pre-dim′; j-ok; bd; lwTy; lwTy-pre; lwTy-dim; lw-ty; Wh-wf-pure)

------------------------------------------------------------------------
-- The surface equality.

ImgEq : Ctx → Tm → Tm → Set
ImgEq Γ t u = ⟦ t ⟧ (η Γ) ≈w ⟦ u ⟧ (η Γ)

Base : Ctx → Tm → Tm → Set
Base Γ t u = Σ Ty λ A → Σ Ty λ B → (Γ ⊢tm t ∶ A) × (Γ ⊢tm u ∶ B) × ImgEq Γ t u

open import CaTTExp.Surface.Generated ∅ side closedS Base public

Unit : Ctx → Tm → Set
Unit Γ p = UnitTw (⟦ p ⟧ (η Γ))

------------------------------------------------------------------------
-- Arithmetic and lookups.

private
  ==-refl : ∀ n → (n ==ℕ n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  <→≢ : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  <→≢ zero    (suc n) _ = refl
  <→≢ (suc i) (suc n) p = <→≢ i n p

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  -- dbl k < dbl (j + k) + 2
  lt-dl : ∀ j k → T (dbl k <ℕ suc (suc (dbl (j + k))))
  lt-dl j zero    = tt
  lt-dl j (suc k) rewrite +-suc j k = lt-dl j k

  -- dbl (suc k) < tL k j
  lt-h : ∀ k j → T (dbl (suc k) <ℕ tL k j)
  lt-h k j = lt-dl j k

  lkₑ-top : ∀ E X i → lenₑ E ≡ i → lookupₑ (E ,ₑ X) i ≡ X
  lkₑ-top E X i refl rewrite ==-refl (lenₑ E) = refl

  lkₑ-skip : ∀ E X i → T (i <ℕ lenₑ E) → lookupₑ (E ,ₑ X) i ≡ lookupₑ E i
  lkₑ-skip E X i p rewrite <→≢ i (lenₑ E) p = refl

  lk-skip : ∀ Γ A i → T (i <ℕ len Γ) → lookup (Γ ▸ A) i ≡ lookup Γ i
  lk-skip Γ A i p rewrite <→≢ i (len Γ) p = refl

  lt-ss : ∀ m → T (m <ℕ suc (suc m))
  lt-ss zero    = tt
  lt-ss (suc m) = lt-ss m

  -- An environment E₀ of length m, extended by three towers.
  lk3-a : ∀ E₀ m A B C → lenₑ E₀ ≡ m → lookupₑ (((E₀ ,ₑ A) ,ₑ B) ,ₑ C) m ≡ A
  lk3-a E₀ m A B C l =
    trans (lkₑ-skip ((E₀ ,ₑ A) ,ₑ B) C m (subst (λ n → T (m <ℕ suc (suc n))) (sym l) (lt-ss m)))
   (trans (lkₑ-skip (E₀ ,ₑ A) B m (subst (λ n → T (m <ℕ suc n)) (sym l) (n<sn m)))
          (lkₑ-top E₀ A m l))

  lk3-c : ∀ E₀ m A B C → lenₑ E₀ ≡ m → lookupₑ (((E₀ ,ₑ A) ,ₑ B) ,ₑ C) (suc (suc m)) ≡ C
  lk3-c E₀ m A B C l = lkₑ-top ((E₀ ,ₑ A) ,ₑ B) C (suc (suc m)) (cong (λ n → suc (suc n)) l)

  -- the top cell of a disk
  lk-Dsk : ∀ n → lookup (D.Dsk n) (dbl n) ≡ just (aL n)
  lk-Dsk n = subst (λ i → lookup (D.Dsk n) i ≡ just (aL n)) (D.len-Sph n) (D.last-lookup (D.Sph n) (aL n))

  lt-Dsk : ∀ n → T (dbl n <ℕ len (D.Dsk n))
  lt-Dsk n = subst (λ m → T (dbl n <ℕ m)) (sym (D.len-Dsk n)) (n<sn (dbl n))

  -- the whiskered cell of BK k j
  lk-cR : ∀ k j → lookup (BK k j) (dbl (nB k j)) ≡ just (aL (nB k j))
  lk-cR k j =
    trans (lk-skip (D.Dsk n ▸ aL k) (hTy k j) (dbl n) (<-suc (dbl n) (len (D.Dsk n)) (lt-Dsk n)))
   (trans (lk-skip (D.Dsk n) (aL k) (dbl n) (lt-Dsk n)) (lk-Dsk n))
    where n = nB k j

  -- the whiskering cell of LK k 0
  lk-hL0 : ∀ k → lookup (LK k 0) (dbl (suc k)) ≡ just (aL (suc k))
  lk-hL0 k =
    trans (lk-skip (D.Dsk (suc k) ▸ aL k) (bLK k 1) (dbl (suc k)) (<-suc (dbl (suc k)) (len (D.Dsk (suc k))) (lt-Dsk (suc k))))
   (trans (lk-skip (D.Dsk (suc k)) (aL k) (dbl (suc k)) (lt-Dsk (suc k))) (lk-Dsk (suc k)))

  -- the whiskered cell of LK k j
  lk-cL : ∀ k j → lookup (LK k j) (tL k j) ≡ just (bLK k (suc j))
  lk-cL k j = subst (λ i → lookup (LK k j) i ≡ just (bLK k (suc j))) (D.len-LPK k j)
                (D.last-lookup (LPK k j) (bLK k (suc j)))

  -- the face substitutions of BK k (j+1), on the two relevant variables
  len-ρK₀ : ∀ k j v → lenₑ (⟦ D.sphSub (aL (nB k j)) ⟧ₛ v) ≡ dbl (nB k j)
  len-ρK₀ k j ρ = trans (lenₑ-⟦⟧ₛ (D.sphSub (aL (nB k j))) ρ)
                        (trans (D.lenₛ-sph (aL (nB k j))) (cong dbl (dim-aL (nB k j))))

  ρK-c : ∀ k j v ρ → lookupₑ (⟦ ρK k j v ⟧ₛ ρ) (dbl (nB k j)) ≡ lookupₑ ρ v
  ρK-c k j v ρ = lk3-a _ (dbl (nB k j)) _ _ _ (len-ρK₀ k j ρ)

  ρK-h : ∀ k j v ρ → lookupₑ (⟦ ρK k j v ⟧ₛ ρ) (suc (zK k j)) ≡ lookupₑ ρ (suc (zK k (suc j)))
  ρK-h k j v ρ = lk3-c _ (dbl (nB k j)) _ _ _ (len-ρK₀ k j ρ)

  -- identity substitutions
  idS-lk : ∀ m ρ i → T (i <ℕ m) → lookupₑ (⟦ D.idS m ⟧ₛ ρ) i ≡ lookupₑ ρ i
  idS-lk m ρ i p =
    trans (lookup-⟦⟧ₛ (D.idS m) ρ i (subst (λ n → T (i <ℕ n)) (sym (D.lenₛ-renS m (λ i → i))) p))
          (cong (λ t → ⟦ t ⟧ ρ) (D.lookup-renS m (λ i → i) i p))

  len-idS : ∀ m ρ → lenₑ (⟦ D.idS m ⟧ₛ ρ) ≡ m
  len-idS m ρ = trans (lenₑ-⟦⟧ₛ (D.idS m) ρ) (D.lenₛ-renS m (λ i → i))

------------------------------------------------------------------------
-- Towers.

-- X is a cell from a to b.
BdS : Tower → Tower → Tower → Set
BdS (base _)     a b = ⊥
BdS (step S U _) a b = (S ≈w a) × (U ≈w b)

Bd→BdS : ∀ X A t u ρ → Bd X (arr A t u) ρ → BdS X (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
Bd→BdS (base _)     A t u ρ ()
Bd→BdS (step S U _) A t u ρ b = b

-- A tower with the boundary of X and the top chain of X is X.
compS : ∀ X a b S U c → BdS X a b → S ≈w a → U ≈w b → c ≈ top X → step S U c ≈w X
compS (base _)       a b S U c ()
compS (step Sx Ux cx) a b S U c (sa , ub) p q r =
  ≈w-trans S a Sx p (≈w-sym Sx a sa) , ≈w-trans U b Ux q (≈w-sym Ux b ub) , r

-- Composition with an identity on the target.
compR0 : ∀ X H a m z c → BdS X a m → BdS H m z → UnitTw H → c ≈ top X → step a z c ≈w X
compR0 X (base _)       a m z c bX () u r
compR0 X (step Sh Uh ch) a m z c bX (sm , uz) u r =
  compS X a m a z c bX (≈w-refl a)
    (≈w-trans z Uh m (≈w-sym Uh z uz) (≈w-trans Uh Sh m (≈w-sym Sh Uh (unit-par Sh Uh ch u)) sm)) r

-- Composition with an identity on the source.
compL0 : ∀ X H a m z c → BdS X m z → BdS H a m → UnitTw H → c ≈ top X → step a z c ≈w X
compL0 X (base _)       a m z c bX () u r
compL0 X (step Sh Uh ch) a m z c bX (sa , um) u r =
  compS X m z a z c bX
    (≈w-trans a Sh m (≈w-sym Sh a sa) (≈w-trans Sh Uh m (unit-par Sh Uh ch u) um)) (≈w-refl z) r

------------------------------------------------------------------------
-- The image of a whisker head is the image of the whiskered cell.

headR : ∀ k j σ ρ → BdEnv (⟦ σ ⟧ₛ ρ) (BK k j) → UnitTw (lookupₑ (⟦ σ ⟧ₛ ρ) (suc (zK k j))) →
        ⟦ coh (BK k j) (wK k j) σ ⟧ ρ ≈w lookupₑ (⟦ σ ⟧ₛ ρ) (dbl (nB k j))
headR k zero σ ρ bρ u =
  compR0 X H (lookupₑ ρ′ (dbl k)) (lookupₑ ρ′ (suc (dbl k))) (lookupₑ ρ′ (zK k 0)) _
    (Bd→BdS X (aL k) (var (dbl k)) (var (suc (dbl k))) ρ′ (bρ _ _ (lk-cR k 0)))
    (Bd→BdS H (aL k) (var (suc (dbl k))) (var (zK k 0)) ρ′ (bρ _ _ (D.lk-hK k 0)))
    u (HR0 k ρ′ u)
  where
  ρ′ = ⟦ σ ⟧ₛ ρ
  X = lookupₑ ρ′ (dbl (nB k 0))
  H = lookupₑ ρ′ (suc (zK k 0))
headR k (suc j) σ ρ bρ u =
  compS X (lookupₑ ρ′ (dbl n)) (lookupₑ ρ′ (suc (dbl n))) _ _ _
    (Bd→BdS X (aL n) (var (dbl n)) (var (suc (dbl n))) ρ′ (bρ _ _ (lk-cR k (suc j))))
    (subst (⟦ coh (BK k j) (wK k j) (ρsK k j) ⟧ ρ′ ≈w_) (ρK-c k j (dbl n) ρ′)
       (headR k j (ρsK k j) ρ′
          (Bd-sub (ρK-wf k j (dbl n) (D.lk-face-s k j)) bρ (wBK k j))
          (subst UnitTw (sym (ρK-h k j (dbl n) ρ′)) u)))
    (subst (⟦ coh (BK k j) (wK k j) (ρtK k j) ⟧ ρ′ ≈w_) (ρK-c k j (suc (dbl n)) ρ′)
       (headR k j (ρtK k j) ρ′
          (Bd-sub (ρK-wf k j (suc (dbl n)) (D.lk-face-t k j)) bρ (wBK k j))
          (subst UnitTw (sym (ρK-h k j (suc (dbl n)) ρ′)) u)))
    (HR k j ρ′ u)
  where
  n = nB k j
  ρ′ = ⟦ σ ⟧ₛ ρ
  X = lookupₑ ρ′ (dbl (nB k (suc j)))

headL : ∀ k j σ ρ → BdEnv (⟦ σ ⟧ₛ ρ) (LK k j) → UnitTw (lookupₑ (⟦ σ ⟧ₛ ρ) (dbl (suc k))) →
        ⟦ coh (LK k j) (lK k j) σ ⟧ ρ ≈w lookupₑ (⟦ σ ⟧ₛ ρ) (tL k j)
headL k zero σ ρ bρ u =
  compL0 X H (lookupₑ ρ′ (dbl k)) (lookupₑ ρ′ (suc (dbl k))) (lookupₑ ρ′ (zK k 0)) _
    (Bd→BdS X (aL k) (var (suc (dbl k))) (var (zK k 0)) ρ′ (bρ _ _ (lk-cL k 0)))
    (Bd→BdS H (aL k) (var (dbl k)) (var (suc (dbl k))) ρ′ (bρ _ _ (lk-hL0 k)))
    u (HL0 k ρ′ u)
  where
  ρ′ = ⟦ σ ⟧ₛ ρ
  X = lookupₑ ρ′ (tL k 0)
  H = lookupₑ ρ′ (dbl (suc k))
headL k (suc j) σ ρ bρ u =
  compS X (lookupₑ ρ′ (tL k j)) (lookupₑ ρ′ (suc (tL k j))) _ _ _
    (Bd→BdS X (bLK k (suc j)) (var (tL k j)) (var (suc (tL k j))) ρ′ (bρ _ _ (lk-cL k (suc j))))
    (subst (⟦ coh (LK k j) (lK k j) (λsK k j) ⟧ ρ′ ≈w_) s-c
       (headL k j (λsK k j) ρ′ (Bd-sub (λsK-wf k j) bρ (wLK k j)) (subst UnitTw (sym s-h) u)))
    (subst (⟦ coh (LK k j) (lK k j) (λtK k j) ⟧ ρ′ ≈w_) t-c
       (headL k j (λtK k j) ρ′ (Bd-sub (λtK-wf k j) bρ (wLK k j)) (subst UnitTw (sym t-h) u)))
    (HL k j ρ′ u)
  where
  ρ′ = ⟦ σ ⟧ₛ ρ
  X = lookupₑ ρ′ (tL k (suc j))
  s-c : lookupₑ (⟦ λsK k j ⟧ₛ ρ′) (tL k j) ≡ lookupₑ ρ′ (tL k j)
  s-c = idS-lk (suc (tL k j)) ρ′ (tL k j) (n<sn (tL k j))
  s-h : lookupₑ (⟦ λsK k j ⟧ₛ ρ′) (dbl (suc k)) ≡ lookupₑ ρ′ (dbl (suc k))
  s-h = idS-lk (suc (tL k j)) ρ′ (dbl (suc k)) (<-suc (dbl (suc k)) (tL k j) (lt-h k j))
  t-c : lookupₑ (⟦ λtK k j ⟧ₛ ρ′) (tL k j) ≡ lookupₑ ρ′ (suc (tL k j))
  t-c = lkₑ-top (⟦ D.idS (tL k j) ⟧ₛ ρ′) _ (tL k j) (len-idS (tL k j) ρ′)
  t-h : lookupₑ (⟦ λtK k j ⟧ₛ ρ′) (dbl (suc k)) ≡ lookupₑ ρ′ (dbl (suc k))
  t-h = trans (lkₑ-skip (⟦ D.idS (tL k j) ⟧ₛ ρ′) _ (dbl (suc k))
                 (subst (λ m → T (dbl (suc k) <ℕ m)) (sym (len-idS (tL k j) ρ′)) (lt-h k j)))
              (idS-lk (tL k j) ρ′ (dbl (suc k)) (lt-h k j))

------------------------------------------------------------------------
-- The unit law.

private
  tm-ctx : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx
  tm-ctx (var-wf w _)       = w
  tm-ctx (coh-wf _ _ _ _ s) = Sg.sub-ctx closedS s
  tm-ctx (cst-wf {()} _ _)

  -- σL sends the whiskering variable to the whiskering cell h.
  mutual
    lkσLp : ∀ k j h x C → dim C ≡ nB k j → lookupₛ (σLp k j h x C) (dbl (suc k)) ≡ h
    lkσLp k zero h x C e =
      trans (D.lk-ext (D.sphSub (hL k x C) ,ₛ h) (tgtK k C) (dbl (suc k))
               (subst (λ m → T (dbl (suc k) <ℕ suc m)) (sym e₁) (n<sn (dbl (suc k)))))
            (subst (λ i → lookupₛ (D.sphSub (hL k x C) ,ₛ h) i ≡ h) e₁ (D.lk-top (D.sphSub (hL k x C)) h))
      where
      e₁ : lenₛ (D.sphSub (hL k x C)) ≡ dbl (suc k)
      e₁ = trans (D.lenₛ-sph (hL k x C)) (cong (λ m → dbl (suc m)) (dim-tyK k C))
    lkσLp k (suc j) h x ⋆            ()
    lkσLp k (suc j) h x (arr C′ s t) e =
      trans (D.lk-ext (σL k j h x s C′) t (dbl (suc k))
               (<-suc (dbl (suc k)) (lenₛ (σLp k j h x C′))
                  (subst (λ m → T (dbl (suc k) <ℕ m)) (sym (lenₛ-σLp k j h x C′ e′)) (lt-h k j))))
            (lkσL k j h x s C′ e′)
      where
      e′ : dim C′ ≡ nB k j
      e′ = cong (λ m → m ∸ 1) e

    lkσL : ∀ k j h x c C → dim C ≡ nB k j → lookupₛ (σL k j h x c C) (dbl (suc k)) ≡ h
    lkσL k j h x c C e =
      trans (D.lk-ext (σLp k j h x C) c (dbl (suc k))
               (subst (λ m → T (dbl (suc k) <ℕ m)) (sym (lenₛ-σLp k j h x C e)) (lt-h k j)))
            (lkσLp k j h x C e)

  wh-eq : ∀ {Γ C s s′ t t′ p q x X} →
          Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ → Γ ⊢tm x ∶ X →
          wh Γ (dim C) p x q ≡ rawW (dim C) (dim X ∸ suc (dim C)) s′ t′ p x X q
  wh-eq dp dq dx rewrite tyOf-ok dp | tyOf-ok dq | tyOf-ok dx = refl

-- The image of (p ◃ₖ x) ▹ₖ q is the image of x when the images of p
-- and q are identities.
wh-img : ∀ {Γ C s s′ t t′ p q x X} →
         Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ →
         Unit Γ p → Unit Γ q →
         Pre (arr C s t) X → Γ ⊢tm x ∶ X →
         ImgEq Γ (wh Γ (dim C) p x q) x
wh-img {Γ} {C} {s} {s′} {t} {t′} {p} {q} {x} {X} dp dq up uq pr dx =
  subst (λ w → ⟦ w ⟧ (η Γ) ≈w ⟦ x ⟧ (η Γ))
        (sym (trans (wh-eq dp dq dx) (cong (λ m → rawW k m s′ t′ p x X q) (j-ok pr))))
        (≈w-trans (⟦ rwT k d L LT t′ q ⟧ (η Γ)) (⟦ L ⟧ (η Γ)) (⟦ x ⟧ (η Γ)) stepR stepL)
  where
  k  = dim C
  d  = depth pr
  L  = lwT k d p s′ x X
  LT = lK k d [ σL k d p s′ x X ]ty
  wΓ = tm-ctx dx
  bX  = bd pr
  bLT = bd (lwTy-pre p s′ pr)
  dp′ : Γ ⊢tm p ∶ hL k s′ X
  dp′ = subst (Γ ⊢tm p ∶_) (sym (cong₂ (λ A b → arr A s′ b) (fst bX) (fst (snd bX)))) dp
  dL : Γ ⊢tm L ∶ LT
  dL = lwT-wf k d dx (pre-dim′ pr) dp′
  eLT : dim LT ≡ nB k d
  eLT = trans (cong dim (lw-ty p s′ x pr)) (lwTy-dim p s′ pr)
  dq′ : Γ ⊢tm q ∶ arr (tyK k LT) (tgtK k LT) t′
  dq′ = subst (Γ ⊢tm q ∶_)
          (sym (trans (cong (λ Z → arr (tyK k Z) (tgtK k Z) t′) (lw-ty p s′ x pr))
                      (cong₂ (λ A b → arr A b t′) (fst bLT) (snd (snd bLT)))))
          dq

  -- right whisker: (p ◃ x) ▹ q has the image of p ◃ x
  lenR : lenₑ (⟦ D.sphSub LT ⟧ₛ (η Γ)) ≡ dbl (nB k d)
  lenR = trans (lenₑ-⟦⟧ₛ (D.sphSub LT) (η Γ)) (trans (D.lenₛ-sph LT) (cong dbl eLT))
  stepR : ⟦ rwT k d L LT t′ q ⟧ (η Γ) ≈w ⟦ L ⟧ (η Γ)
  stepR = subst (⟦ rwT k d L LT t′ q ⟧ (η Γ) ≈w_) (lk3-a _ (dbl (nB k d)) _ _ _ lenR)
            (headR k d (σR L LT t′ q) (η Γ)
               (Bd-sub (σR-wf k d dL eLT dq′) (BdEnv-η wΓ) (wBK k d))
               (subst UnitTw (sym (lk3-c _ (dbl (nB k d)) _ _ _ lenR)) uq))

  -- left whisker: p ◃ x has the image of x
  lenL : lenₑ (⟦ σLp k d p s′ X ⟧ₛ (η Γ)) ≡ tL k d
  lenL = trans (lenₑ-⟦⟧ₛ (σLp k d p s′ X) (η Γ)) (lenₛ-σLp k d p s′ X (pre-dim′ pr))
  ltL : T (dbl (suc k) <ℕ lenₛ (σL k d p s′ x X))
  ltL = <-suc (dbl (suc k)) (lenₛ (σLp k d p s′ X))
          (subst (λ m → T (dbl (suc k) <ℕ m)) (sym (lenₛ-σLp k d p s′ X (pre-dim′ pr))) (lt-h k d))
  hL-eq : lookupₑ (⟦ σL k d p s′ x X ⟧ₛ (η Γ)) (dbl (suc k)) ≡ ⟦ p ⟧ (η Γ)
  hL-eq = trans (lookup-⟦⟧ₛ (σL k d p s′ x X) (η Γ) (dbl (suc k)) ltL)
                (cong (λ w → ⟦ w ⟧ (η Γ)) (lkσL k d p s′ x X (pre-dim′ pr)))
  stepL : ⟦ L ⟧ (η Γ) ≈w ⟦ x ⟧ (η Γ)
  stepL = subst (⟦ L ⟧ (η Γ) ≈w_) (lkₑ-top (⟦ σLp k d p s′ X ⟧ₛ (η Γ)) (⟦ x ⟧ (η Γ)) (tL k d) lenL)
            (headL k d (σL k d p s′ x X) (η Γ)
               (Bd-sub (σL-wf k d dx (pre-dim′ pr) dp′) (BdEnv-η wΓ) (wLK k d))
               (subst UnitTw (sym hL-eq) up))

-- TheoremB's Wh-≈.
Wh-≈ : ∀ {Γ C s s′ t t′ p q x X} →
       Γ ⊢tm p ∶ arr C s′ s → Γ ⊢tm q ∶ arr C t t′ →
       Unit Γ p → Unit Γ q →
       Pre (arr C s t) X → Γ ⊢tm x ∶ X →
       Γ ∣ wh Γ (dim C) p x q ≈g x
Wh-≈ dp dq up uq pr dx =
  g-base (_ , _ , Wh-wf-pure E (λ {Γ} {A} {A′} {a} {a′} {b} {b′} → inv-arr {Γ} {A} {A′} {a} {a′} {b} {b′})
                              dim-≈ Unit dp dq pr dx ,
          dx , wh-img dp dq up uq pr dx)

------------------------------------------------------------------------
-- Theorem B for this surface equality, every hypothesis discharged.

module Instance where
  open Hyp E (λ {Γ} {A} {A′} {a} {a′} {b} {b′} → inv-arr {Γ} {A} {A′} {a} {a′} {b} {b′})
           dim-≈ tm-ty Unit wh public
  open Thm (Wh-wf-pure E (λ {Γ} {A} {A′} {a} {a′} {b} {b′} → inv-arr {Γ} {A} {A′} {a} {a′} {b} {b′})
                       dim-≈ Unit)
           (λ {Γ} {C} {s} {s′} {t} {t′} {p} {q} {x} {X} → Wh-≈ {Γ} {C} {s} {s′} {t} {t′} {p} {q} {x} {X}) public
