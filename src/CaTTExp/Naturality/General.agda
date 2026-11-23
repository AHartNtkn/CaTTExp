------------------------------------------------------------------------
-- A naturality filler family for coherences of every dimension
-- (ledger C1d, item 2), well typed relative to relative coherence.
--
-- For a pasting coherence c = coh Q B id and an up-closed selection Y,
-- the filler c↑ is a 3-term (in general an (n+1)-term) in the cylinder
-- context Q↑Y between the two parallel cells a_c and b_c. Conjecture N
-- (notes/relative-coherence.md §4) says such a cell exists; Proposition
-- R reduces it to relative coherence on Q↑Y. This module takes that
-- reduction at face value and defines the filler as the answer of the
-- relative-coherence procedure itself:
--
--   Kω Q B Y = K₁ Q B Y                              (dim B = 1)
--   Kω Q B Y = rcS (a_c) (b_c)  on Q↑Y               (dim B ≥ 2)
--
-- where K₁ is the explicit dimension-1 family of
-- CaTTExp.Naturality.DimOne, rcS is CaTTExp.RCProc.rcS, and the typing
-- derivations rcS needs are produced by the certified checker
-- (CaTTExp.Completeness: dec-ctx, dec-tm). The boundary a_c, b_c of the
-- query mentions the cylinders of B's boundary terms, so the family is
-- defined by recursion on the size of B (`Kb`, `Kω`, `stab`).
--
-- What is proved, with no postulate:
--
--   okAll : FillerOK Kω Good
--
-- where Good Q B holds when every coherence occurring in B, and B itself,
-- is either 1-dimensional or satisfies
--
--   RCq Q B : for every admissible Y, rcS answers the query
--             (a_c, b_c) on Q↑Y for all typing derivations of its sides.
--
-- So for coherences of dimension ≥ 2 the theorem is CONDITIONAL on RCq:
-- it holds exactly where the relative-coherence procedure answers the
-- cylinder query. Nothing here proves RCq for any coherence of
-- dimension ≥ 2. Discharging it needs (i) totality of rcS on parallel
-- 2-cells with equal strict image (Theorem A, ledger S20 / RC thread),
-- (ii) equality of the strict images of a_c and b_c, and (iii) for
-- dimension ≥ 3, RC(n) (the descent, RCGEN). See open-issues C1d.
--
-- RCq is NOT expected to hold for a composition c (dim Q = dim c) with
-- a selected top cell q: then a_c and b_c have different strict images
-- (they differ by the generator q↑), so Theorem A does not apply and
-- nothing will discharge RCq there. okAll gives nothing for those c. They need
-- the layered filler of Proposition R (relative-coherence.md §4.1), not
-- yet built. Kω is the intended filler for coherences, and for
-- compositions whose top cells are all unselected.
--
-- For terms all of whose coherences are 1-dimensional (in particular
-- every term of dimension ≤ 1) Good holds outright (`low-h`), so
-- `cylω-low` is unconditional, as in DimOne.
------------------------------------------------------------------------
module CaTTExp.Naturality.General where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTm)
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Completeness ∅ cattSide (λ ()) (λ ()) as Ch
open Ch using (Dec; yes; no)
open import CaTTExp.Derived using (idS; id-wf; id-ty; tm-ctx)
open import CaTTExp.DerivedBoundary using (dim[])
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn; ≤-<-trans; <-≤-trans; <suc-≢)
open import CaTTExp.GraphFillerTotal using (⋆-var)
open import CaTTExp.GraphFillerTotal.Chains using (chain-side)
open import CaTTExp.RCProc using (rcS; Ans)
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Typing using (UpSel; module Hyp; module Main)
open import CaTTExp.Naturality.Boundary using (module Typed)
open import CaTTExp.Naturality.Commute using (Scoped; eq-sound)
open import CaTTExp.Naturality.CylCtx using (module CW)
open import CaTTExp.Naturality.DimOne
  using (K₀; K₁; K₁-sc; K₁-ok; clean; clean-sc; clean-eq; module Indep; LowCtx; low-chain)

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  cong₅ : ∀ {A B C D E F : Set} (f : A → B → C → D → E → F) {a a' b b' c c' d d' e e'} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f a b c d e ≡ f a' b' c' d' e'
  cong₅ f refl refl refl refl refl = refl

  if-cong : ∀ {X : Set} b {x x' y y' : X} → x ≡ x' → y ≡ y' → (if b then x else y) ≡ (if b then x' else y')
  if-cong b refl refl = refl

------------------------------------------------------------------------
-- Syntactic size.

mutual
  sizeTm : Tm → Nat
  sizeTm (var _)     = 0
  sizeTm (coh _ B γ) = suc (sizeTy B + sizeS γ)
  sizeTm (cst _)     = 0

  sizeTy : Ty → Nat
  sizeTy ⋆           = 0
  sizeTy (arr A s u) = suc (sizeTy A + sizeTm s + sizeTm u)

  sizeS : Sub → Nat
  sizeS ⟨⟩       = 0
  sizeS (γ ,ₛ t) = suc (sizeS γ + sizeTm t)

private
  le-l : ∀ a b → T (a <ℕ suc (a + b))
  le-l zero    b = tt
  le-l (suc a) b = le-l a b

  le-r : ∀ a b → T (b <ℕ suc (a + b))
  le-r zero    b = n<sn b
  le-r (suc a) b = <-suc b (suc (a + b)) (le-r a b)

  -- a + b ≤ n gives a ≤ n and b ≤ n (written with < suc).
  +≤l : ∀ a b n → T (a + b <ℕ suc n) → T (a <ℕ suc n)
  +≤l a b n p = ≤-<-trans a (a + b) (suc n) (le-l a b) p

  +≤r : ∀ a b n → T (a + b <ℕ suc n) → T (b <ℕ suc n)
  +≤r a b n p = ≤-<-trans b (a + b) (suc n) (le-r a b) p

  -- suc m ≤ n gives m < n.
  s≤ : ∀ m n → T (suc m <ℕ suc n) → T (m <ℕ n)
  s≤ m n p = p

------------------------------------------------------------------------
-- Families that agree on a class of coherences have the same cylinders
-- on terms and types built from that class.

module Agree (K K' : Filler) (Ok : Ctx → Ty → Set)
             (agree : ∀ Q B Y → Ok Q B → K Q B Y ≡ K' Q B Y) where
  module C  = Cyl K
  module C' = Cyl K'

  mutual
    OTm : Tm → Set
    OTm (var _)     = ⊤
    OTm (coh Q B γ) = Ok Q B × OS γ
    OTm (cst _)     = ⊤

    OS : Sub → Set
    OS ⟨⟩       = ⊤
    OS (γ ,ₛ t) = OS γ × OTm t

  OTy : Ty → Set
  OTy ⋆           = ⊤
  OTy (arr A s u) = OTy A × OTm s × OTm u

  OCtx : Ctx → Set
  OCtx ε       = ⊤
  OCtx (Q ▸ A) = OCtx Q × OTy A

  -- Pasting contexts have only variables in their types.
  ps-o : ∀ {Q x A} → Q ⊢ps x ∶ A → OCtx Q × OTy A
  ps-o pss     = (tt , tt) , tt
  ps-o (pse d) = let (oQ , oA) = ps-o d in ((oQ , oA) , (oA , tt , tt)) , (oA , tt , tt)
  ps-o (psd d) = let (oQ , (oA , _ , _)) = ps-o d in oQ , oA

  ps-oc : ∀ {Q} → Q ⊢ps → OCtx Q
  ps-oc (ps d) = fst (ps-o d)

  mutual
    cyl-ag : ∀ D t → OTm t → C.cyl D t ≡ C'.cyl D t
    cyl-ag D (var x)     _        = refl
    cyl-ag D (coh Q B γ) (o , os) = cong₂ _[_]tm (agree Q B (C.mask D γ) o) (liftS-ag D γ os)
    cyl-ag D (cst ())    _

    liftS-ag : ∀ D γ → OS γ → C.liftS D γ ≡ C'.liftS D γ
    liftS-ag D ⟨⟩       _         = refl
    liftS-ag D (γ ,ₛ t) (os , ot) =
      cong₂ (λ ρ c → liftOne ρ (t [ mm D ]tm) (t [ mp D ]tm) c (C.touched D t)) (liftS-ag D γ os) (cyl-ag D t ot)

  private
    o-if : ∀ b {x y} → OTm x → OTm y → OTm (if b then x else y)
    o-if true  p _ = p
    o-if false _ q = q

    o-ifTy : ∀ b {x y} → OTy x → OTy y → OTy (if b then x else y)
    o-ifTy true  p _ = p
    o-ifTy false _ q = q

  o-tgt : ∀ k A → OTy A → OTm (tgtAt k A)
  o-tgt k ⋆           _              = tt
  o-tgt k (arr A s u) (oA , os , ou) = o-if (k ==ℕ dim A) ou (o-tgt k A oA)

  o-src : ∀ k A → OTy A → OTm (srcAt k A)
  o-src k ⋆           _              = tt
  o-src k (arr A s u) (oA , os , ou) = o-if (k ==ℕ dim A) os (o-src k A oA)

  o-base : ∀ k A → OTy A → OTy (baseAt k A)
  o-base k ⋆           _ = tt
  o-base k (arr A s u) o = o-ifTy (k ==ℕ suc (dim A)) o (o-base k A (fst o))

  module _ (D : Datum) where
    mutual
      P-ag : ∀ k t A → OTy A → C.P D k t A ≡ C'.P D k t A
      P-ag zero    t A oA = refl
      P-ag (suc k) t A oA =
        cong₅ (λ p tp l c b → rwI k (dim A) p tp l c b)
          (P-ag k t A oA) (TP-ag k A oA) (L-ag k (tgtAt k A) (baseAt k A) (o-base k A oA))
          (cyl-ag D (tgtAt k A) (o-tgt k A oA)) refl

      TP-ag : ∀ k A → OTy A → C.TP D k A ≡ C'.TP D k A
      TP-ag zero    A           _              = refl
      TP-ag (suc k) ⋆           _              = refl
      TP-ag (suc k) (arr A s u) o@(oA , _ , _) =
        if-cong (k ==ℕ dim A)
          (cong₃ arr (TP-ag k A oA) (P-ag k s A oA) (L-ag k u A oA))
          (cong₃ arr (TP-ag (suc k) A oA) (P-ag (suc k) s A oA) (P-ag (suc k) u A oA))

      L-ag : ∀ k t A → OTy A → C.L D k t A ≡ C'.L D k t A
      L-ag zero    t A oA = refl
      L-ag (suc k) t A oA =
        cong₅ (λ c p l tl b → lwI k (dim A) c p l tl b)
          (cyl-ag D (srcAt k A) (o-src k A oA)) (P-ag k (srcAt k A) (baseAt k A) (o-base k A oA))
          (L-ag k t A oA) (TL-ag k A oA) refl

      TL-ag : ∀ k A → OTy A → C.TL D k A ≡ C'.TL D k A
      TL-ag zero    A           _              = refl
      TL-ag (suc k) ⋆           _              = refl
      TL-ag (suc k) (arr A s u) o@(oA , _ , _) =
        if-cong (k ==ℕ dim A)
          (cong₃ arr (TP-ag k A oA) (P-ag k s A oA) (L-ag k u A oA))
          (cong₃ arr (TL-ag (suc k) A oA) (L-ag (suc k) s A oA) (L-ag (suc k) u A oA))

    cylTy-ag : ∀ t A → OTy A → C.cylTy D t A ≡ C'.cylTy D t A
    cylTy-ag t A oA = cong₃ arr (TP-ag (dim A) A oA) (P-ag (dim A) t A oA) (L-ag (dim A) t A oA)

  open Indep K K' using (gm-indep; gp-indep; gen-indep)

  cylTy-gen : ∀ Y t A → OTy A → C.cylTy (C.gen Y) t A ≡ C'.cylTy (C'.gen Y) t A
  cylTy-gen Y t A oA = trans (cong (λ G → C.cylTy G t A) (gen-indep Y)) (cylTy-ag (C'.gen Y) t A oA)

  cylCtx-ag : ∀ Q Y → OCtx Q → C.cylCtx Q Y ≡ C'.cylCtx Q Y
  cylCtx-ag ε       Y           _          = refl
  cylCtx-ag (Q ▸ A) ◇           _          = refl
  cylCtx-ag (Q ▸ A) (Y ◂ true)  (oQ , oA)  =
    go (cylCtx-ag Q Y oQ) (gm-indep Y) (gp-indep Y) (cylTy-gen (Y ◂ true) (var (len Q)) A oA)
    where
    go : ∀ {Γ Γ' X X' Z Z' U U'} → Γ ≡ Γ' → X ≡ X' → Z ≡ Z' → U ≡ U' →
         Γ ▸ A [ X ]ty ▸ A [ Z ]ty ▸ U ≡ Γ' ▸ A [ X' ]ty ▸ A [ Z' ]ty ▸ U'
    go refl refl refl refl = refl
  cylCtx-ag (Q ▸ A) (Y ◂ false) (oQ , oA)  = cong₂ (λ Γ X → Γ ▸ A [ X ]ty) (cylCtx-ag Q Y oQ) (gm-indep Y)

ty-inv : ∀ {Γ X a b} → Γ ⊢ty arr X a b → (Γ ⊢tm a ∶ X) × (Γ ⊢tm b ∶ X)
ty-inv (arr-wf da db) = da , db

------------------------------------------------------------------------
-- The solver: run the certified checker on the two sides of a query,
-- then rcS on the derivations it returns.

private
  fromAns : ∀ {Γ X a b} → Maybe (Ans Γ X a b) → Tm
  fromAns (just (w , _)) = w
  fromAns nothing        = junk

  solveD : ∀ Γ X a b → Dec (Γ ⊢tm a ∶ X) → Dec (Γ ⊢tm b ∶ X) → Tm
  solveD Γ X a b (yes da) (yes db) = fromAns (rcS da db)
  solveD Γ X a b _        _        = junk

  solveW : ∀ Γ X a b → Dec (Γ ⊢ctx) → Tm
  solveW Γ X a b (yes w) = solveD Γ X a b (Ch.dec-tm Γ w a X) (Ch.dec-tm Γ w b X)
  solveW Γ X a b (no _)  = junk

solve : Ctx → Ty → Tm → Tm → Tm
solve Γ X a b = solveW Γ X a b (Ch.dec-ctx Γ)

solveTy : Ctx → Ty → Tm
solveTy Γ ⋆           = junk
solveTy Γ (arr X a b) = solve Γ X a b

-- The hypothesis under which the solver answers: rcS answers the query
-- for every pair of derivations of its sides.
RCAt : Ctx → Ty → Set
RCAt Γ ⋆           = ⊤
RCAt Γ (arr X a b) = (da : Γ ⊢tm a ∶ X) (db : Γ ⊢tm b ∶ X) → T (is-just (rcS da db))

solve-ok : ∀ {Γ X a b} → Γ ⊢tm a ∶ X → Γ ⊢tm b ∶ X → RCAt Γ (arr X a b) → Γ ⊢tm solve Γ X a b ∶ arr X a b
solve-ok {Γ} {X} {a} {b} da db rc = goW (Ch.dec-ctx Γ)
  where
  goA : (m : Maybe (Ans Γ X a b)) → T (is-just m) → Γ ⊢tm fromAns m ∶ arr X a b
  goA (just (w , dw)) _ = dw

  goD : (p : Dec (Γ ⊢tm a ∶ X)) (q : Dec (Γ ⊢tm b ∶ X)) → Γ ⊢tm solveD Γ X a b p q ∶ arr X a b
  goD (yes da') (yes db') = goA (rcS da' db') (rc da' db')
  goD (yes _)   (no nb)   = ⊥-elim (nb db)
  goD (no na)   _         = ⊥-elim (na da)

  goW : (p : Dec (Γ ⊢ctx)) → Γ ⊢tm solveW Γ X a b p ∶ arr X a b
  goW (yes w) = goD (Ch.dec-tm Γ w a X) (Ch.dec-tm Γ w b X)
  goW (no nw) = ⊥-elim (nw (tm-ctx da))

------------------------------------------------------------------------
-- The family, by recursion on the size of B.

isDim1 : Ty → Bool
isDim1 (arr ⋆ _ _) = true
isDim1 _           = false

-- One level: the filler of c = coh Q B id, computed with the cylinders
-- of K (which is only consulted on the coherences in B's boundary).
stepRaw : Filler → Filler
stepRaw K Q B Y =
  if isDim1 B then K₁ Q B Y
  else solveTy (Cyl.cylCtx K Q Y) (Cyl.cylTy K (Cyl.gen K Y) (Cyl.cohId K Q B) B)

step : Filler → Filler
step K Q B Y = clean (cnt Y) (stepRaw K Q B Y)

-- Kb n is correct on coherences of size < n.
Kb : Nat → Filler
Kb zero    = K₀
Kb (suc n) Q B Y = if sizeTy B ==ℕ n then step (Kb n) Q B Y else Kb n Q B Y

Kω : Filler
Kω Q B Y = step (Kb (sizeTy B)) Q B Y

Kω-sc : Scoped Kω
Kω-sc Q B Y = clean-sc (cnt Y) (stepRaw (Kb (sizeTy B)) Q B Y)

stab : ∀ m Q B Y → T (sizeTy B <ℕ m) → Kb m Q B Y ≡ Kω Q B Y
stab zero    Q B Y ()
stab (suc m) Q B Y p = go (sizeTy B ==ℕ m) refl
  where
  go : ∀ v → (sizeTy B ==ℕ m) ≡ v → Kb (suc m) Q B Y ≡ Kω Q B Y
  go true  e = trans (cong (λ v → if v then step (Kb m) Q B Y else Kb m Q B Y) e)
                     (cong (λ n → step (Kb n) Q B Y) (sym (eq-sound {sizeTy B} {m} e)))
  go false e = trans (cong (λ v → if v then step (Kb m) Q B Y else Kb m Q B Y) e)
                     (stab m Q B Y (<suc-≢ (sizeTy B) m p e))

-- Kb n and Kω have the same cylinders on terms built from coherences
-- of size < n.
module AgB (n : Nat) = Agree (Kb n) Kω (λ _ B → T (sizeTy B <ℕ n)) (λ Q B Y p → stab n Q B Y p)

-- K₁ and Kω have the same cylinders on terms with no coherences.
module Ag1 = Agree K₁ Kω (λ _ _ → ⊥) (λ _ _ _ ())

-- A term of type ⋆ is a variable, so has no coherence in it.
o⋆ : ∀ {Γ t} → Γ ⊢tm t ∶ ⋆ → Ag1.OTm t
o⋆ {t = t} d = go (⋆-var d refl)
  where
  go : Σ Nat (λ j → t ≡ var j) → Ag1.OTm t
  go (_ , refl) = tt

-- Every term of size ≤ n is built from coherences of size < n.
module _ (n : Nat) where
  open AgB n
  mutual
    b-tm : ∀ t → T (sizeTm t <ℕ suc n) → OTm t
    b-tm (var _)     _ = tt
    b-tm (coh Q B γ) p = ≤-<-trans (sizeTy B) (sizeTy B + sizeS γ) n (le-l (sizeTy B) (sizeS γ)) p
                       , b-s γ (<-suc (sizeS γ) n (≤-<-trans (sizeS γ) (sizeTy B + sizeS γ) n (le-r (sizeTy B) (sizeS γ)) p))
    b-tm (cst _)     _ = tt

    b-s : ∀ γ → T (sizeS γ <ℕ suc n) → OS γ
    b-s ⟨⟩       _ = tt
    b-s (γ ,ₛ t) p = b-s γ (+≤l (sizeS γ) (sizeTm t) n (<-suc (sizeS γ + sizeTm t) n p))
                   , b-tm t (+≤r (sizeS γ) (sizeTm t) n (<-suc (sizeS γ + sizeTm t) n p))

  b-ty : ∀ A → T (sizeTy A <ℕ suc n) → OTy A
  b-ty ⋆           _ = tt
  b-ty (arr A s u) p =
    b-ty A (+≤l (sizeTy A) (sizeTm s) n p1) , b-tm s (+≤r (sizeTy A) (sizeTm s) n p1) , b-tm u (+≤r (sizeTy A + sizeTm s) (sizeTm u) n p0)
    where
    p0 = <-suc (sizeTy A + sizeTm s + sizeTm u) n p
    p1 = +≤l (sizeTy A + sizeTm s) (sizeTm u) n p0

------------------------------------------------------------------------
-- The hypothesis, and the class of coherences it covers.

-- rcS answers the cylinder query of c = coh Q B id on Q↑Y, for every
-- admissible Y.
RCq : Ctx → Ty → Set
RCq Q B = ∀ Y → lenSel Y ≡ len Q → UpSel Q Y → T (anySel Y) →
          RCAt (Cyl.cylCtx Kω Q Y) (Cyl.cylTy Kω (Cyl.gen Kω Y) (Cyl.cohId Kω Q B) B)

-- 1-dimensional coherences need nothing; the others need RCq.
Gd : Ctx → Ty → Set
Gd Q ⋆                       = ⊥
Gd Q (arr ⋆ _ _)             = ⊤
Gd Q B@(arr (arr _ _ _) _ _) = RCq Q B

-- Hereditarily: every coherence occurring in a term or type is Gd.
mutual
  HTm : Tm → Set
  HTm (var _)     = ⊤
  HTm (coh Q B γ) = (Gd Q B × HTy B) × HS γ
  HTm (cst _)     = ⊤

  HTy : Ty → Set
  HTy ⋆           = ⊤
  HTy (arr A s u) = HTy A × HTm s × HTm u

  HS : Sub → Set
  HS ⟨⟩       = ⊤
  HS (γ ,ₛ t) = HS γ × HTm t

Good : Ctx → Ty → Set
Good Q B = Gd Q B × HTy B

-- Good restricted to sizes below n, for the induction.
GoodB : Nat → Ctx → Ty → Set
GoodB n Q B = Good Q B × T (sizeTy B <ℕ n)

open Hyp Kω using (AllGood; AllGoodS; FillerOK)

------------------------------------------------------------------------
-- The induction step: Kω is well typed on c = coh Q B id, given that it
-- is on every Good coherence smaller than B.

module _ {Q A s u Y} (pQ : Q ⊢ps) (wQ : Q ⊢ctx) (wB : Q ⊢ty arr A s u) (side : T (cattSide Q A s u))
         (lY : lenSel Y ≡ len Q) (upY : UpSel Q Y) (anyY : T (anySel Y)) (g : Good Q (arr A s u))
         (IH : FillerOK (GoodB (sizeTy (arr A s u)))) where
  private
    B  = arr A s u
    sz = sizeTy B
    c  = Cyl.cohId Kω Q B
    module Cω = Cyl Kω
    module CWω = CW Kω Kω-sc (GoodB sz) IH

    Δ  = Cω.cylCtx Q Y

    dc : Q ⊢tm c ∶ B
    dc = subst (Q ⊢tm c ∶_) (id-ty (len Q) B (Sb.ty-sc closed wB)) (coh-wf pQ wQ wB side (id-wf wQ))

    mutual
      h-tm : ∀ t → T (sizeTm t <ℕ suc sz) → HTm t → AllGood (GoodB sz) t
      h-tm (var _)     _ _ = tt
      h-tm (coh Q' B' γ) p ((gd , hB) , hγ) =
        ((gd , hB) , ≤-<-trans (sizeTy B') (sizeTy B' + sizeS γ) sz (le-l (sizeTy B') (sizeS γ)) p)
        , h-s γ (<-suc (sizeS γ) sz (≤-<-trans (sizeS γ) (sizeTy B' + sizeS γ) sz (le-r (sizeTy B') (sizeS γ)) p)) hγ
      h-tm (cst _)     _ _ = tt

      h-s : ∀ γ → T (sizeS γ <ℕ suc sz) → HS γ → AllGoodS (GoodB sz) γ
      h-s ⟨⟩       _ _ = tt
      h-s (γ ,ₛ t) p (hγ , ht) =
        h-s γ (+≤l (sizeS γ) (sizeTm t) sz (<-suc (sizeS γ + sizeTm t) sz p)) hγ
        , h-tm t (+≤r (sizeS γ) (sizeTm t) sz (<-suc (sizeS γ + sizeTm t) sz p)) ht

    h-ty : ∀ A' → T (sizeTy A' <ℕ suc sz) → HTy A' → CWω.GoodTy A'
    h-ty ⋆            _ _ = tt
    h-ty (arr A' s' u') p (hA , hs , hu) =
      h-ty A' (+≤l (sizeTy A') (sizeTm s') sz p1) hA
      , h-tm s' (+≤r (sizeTy A') (sizeTm s') sz p1) hs
      , h-tm u' (+≤r (sizeTy A' + sizeTm s') (sizeTm u') sz p0) hu
      where
      p0 = <-suc (sizeTy A' + sizeTm s' + sizeTm u') sz p
      p1 = +≤l (sizeTy A' + sizeTm s') (sizeTm u') sz p0

    -- Pasting contexts have only variables in their types.
    ps-good : ∀ {Q' x A'} → Q' ⊢ps x ∶ A' → CWω.GoodCtx Q' × CWω.GoodTy A'
    ps-good pss     = (tt , tt) , tt
    ps-good (pse d) = let (gQ , gA) = ps-good d in ((gQ , gA) , (gA , tt , tt)) , (gA , tt , tt)
    ps-good (psd d) = let (gQ , (gA , _ , _)) = ps-good d in gQ , gA

    ps-goodc : ∀ {Q'} → Q' ⊢ps → CWω.GoodCtx Q'
    ps-goodc (ps d) = fst (ps-good d)

    gQ : CWω.GoodCtx Q
    gQ = ps-goodc pQ

    IHc = CWω.cylCtx-ok Q Y wQ gQ lY upY

    -- The query (a_c, b_c) is well typed in Q↑Y.
    wT : Δ ⊢ty Cω.cylTy (Cω.gen Y) c B
    wT = Typed.cylTy-wf Kω (CWω.toBase (snd IHc)) dc (CWω.bd-from (snd IHc) B wB (h-ty B (n<sn sz) (snd g)))

    lenΔ : len Δ ≡ cnt Y
    lenΔ = CWω.len-cylCtx Q Y lY

    finish : ∀ {w} → Δ ⊢tm w ∶ Cω.cylTy (Cω.gen Y) c B → Δ ⊢tm clean (cnt Y) w ∶ Cω.cylTy (Cω.gen Y) c B
    finish {w} dw = subst (λ v → Δ ⊢tm v ∶ Cω.cylTy (Cω.gen Y) c B)
                      (sym (clean-eq (cnt Y) w (subst (λ m → ScTm m w) lenΔ (Sb.tm-sc closed dw)))) dw

    -- dimension ≥ 2: the solver, on Kb sz's cylinders, which are Kω's.
    hi : ∀ A₀ s₀ u₀ → A ≡ arr A₀ s₀ u₀ →
         Δ ⊢tm solveTy (Cyl.cylCtx (Kb sz) Q Y) (Cyl.cylTy (Kb sz) (Cyl.gen (Kb sz) Y) c B)
            ∶ Cω.cylTy (Cω.gen Y) c B
    hi A₀ s₀ u₀ refl =
      subst₂' (AgB.cylCtx-ag sz Q Y (AgB.ps-oc sz pQ))
              (AgB.cylTy-gen sz Y c B (b-ty sz B (n<sn sz)))
              (solve-ok da db (fst g Y lY upY anyY))
      where
      da = fst (ty-inv wT)
      db = snd (ty-inv wT)
      subst₂' : ∀ {Γ X} → Γ ≡ Δ → X ≡ Cω.cylTy (Cω.gen Y) c B →
                Δ ⊢tm solveTy Δ (Cω.cylTy (Cω.gen Y) c B) ∶ Cω.cylTy (Cω.gen Y) c B →
                Δ ⊢tm solveTy Γ X ∶ Cω.cylTy (Cω.gen Y) c B
      subst₂' refl refl d = d

  step-ok : Δ ⊢tm Kω Q B Y ∶ Cω.cylTy (Cω.gen Y) c B
  step-ok = go A refl
    where
    go : ∀ A' → A ≡ A' → Δ ⊢tm Kω Q B Y ∶ Cω.cylTy (Cω.gen Y) c B
    go ⋆ refl = finish (subst₂' (Ag1.cylCtx-ag Q Y (Ag1.ps-oc pQ)) (Ag1.cylTy-gen Y c B oB)
                         (K₁-ok pQ wQ wB side lY upY anyY tt))
      where
      oB : Ag1.OTy B
      oB = tt , o⋆ (fst (ty-inv wB)) , o⋆ (snd (ty-inv wB))
      subst₂' : ∀ {Γ X} → Γ ≡ Δ → X ≡ Cω.cylTy (Cω.gen Y) c B →
                Γ ⊢tm K₁ Q B Y ∶ X → Δ ⊢tm K₁ Q B Y ∶ Cω.cylTy (Cω.gen Y) c B
      subst₂' refl refl d = d
    go (arr A₀ s₀ u₀) refl = finish (hi A₀ s₀ u₀ refl)

------------------------------------------------------------------------
-- The family is well typed on every Good coherence.

okB : ∀ n → FillerOK (GoodB n)
okB zero    pQ wQ wB side lY upY anyY (g , ())
okB (suc n) {Q} {A} {s} {u} {Y} pQ wQ wB side lY upY anyY (g , p) =
  step-ok pQ wQ wB side lY upY anyY g IH'
  where
  IH' : FillerOK (GoodB (sizeTy (arr A s u)))
  IH' {Q'} {A'} {s'} {u'} {Y'} pQ' wQ' wB' side' lY' upY' anyY' (g' , p') =
    okB n pQ' wQ' wB' side' lY' upY' anyY' (g' , <-≤-trans (sizeTy (arr A' s' u')) (sizeTy (arr A s u)) n p' p)

okAll : FillerOK Good
okAll {Q} {A} {s} {u} {Y} pQ wQ wB side lY upY anyY g =
  okB (suc (sizeTy (arr A s u))) pQ wQ wB side lY upY anyY (g , n<sn (sizeTy (arr A s u)))

-- The cylinder of every term whose coherences are hereditarily Good,
-- for every valid datum.
module Cylω = Main Kω Kω-sc Good okAll

mutual
  h-ag : ∀ t → HTm t → AllGood Good t
  h-ag (var _)     _          = tt
  h-ag (coh Q B γ) (gB , hγ)  = gB , h-agS γ hγ
  h-ag (cst _)     _          = tt

  h-agS : ∀ γ → HS γ → AllGoodS Good γ
  h-agS ⟨⟩       _         = tt
  h-agS (γ ,ₛ t) (hγ , ht) = h-agS γ hγ , h-ag t ht

cylω-wf : ∀ {D Γ Δ t A} → Hyp.ValidD Kω D Γ Δ → Γ ⊢tm t ∶ A → HTm t →
          T (Cyl.touched Kω D t) → Δ ⊢tm Cyl.cyl Kω D t ∶ Cyl.cylTy Kω D t A
cylω-wf {t = t} V dt ht q = Cylω.cyl-wf V dt (h-ag t ht) q

------------------------------------------------------------------------
-- Terms of dimension ≤ 1 are Good outright (no hypothesis), as in
-- CaTTExp.Naturality.DimOne.

private
  h⋆ : ∀ {Γ t} → Γ ⊢tm t ∶ ⋆ → HTm t
  h⋆ {t = t} d = go (⋆-var d refl)
    where
    go : Σ Nat (λ j → t ≡ var j) → HTm t
    go (_ , refl) = tt

  low-coh : ∀ {Q s u} → Q ⊢ps → Q ⊢ty arr ⋆ s u → T (cattSide Q ⋆ s u) → LowCtx Q
  low-coh pQ (arr-wf ds du) side with ⋆-var ds refl | ⋆-var du refl
  ... | i , refl | i' , refl with chain-side pQ side
  ... | k , refl , _ = low-chain k

mutual
  low-h : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (dim A <ℕ 2) → HTm t
  low-h (var-wf _ _) _ = tt
  low-h (coh-wf {A = ⋆} pQ wQ wB side sγ) p =
    (tt , (tt , h⋆ (fst (ty-inv wB)) , h⋆ (snd (ty-inv wB)))) , low-hS sγ (low-coh pQ wB side)
  low-h (coh-wf {A = arr _ _ _} pQ wQ wB side sγ) ()
  low-h (cst-wf {()} _ _) _

  low-hS : ∀ {Γ γ Q} → Γ ⊢sub γ ∶ Q → LowCtx Q → HS γ
  low-hS (⟨⟩-wf _)                     _        = tt
  low-hS (,-wf {σ = σ} {A = B} sγ dt) (lQ , lB) =
    low-hS sγ lQ , low-h dt (subst (λ n → T (n <ℕ 2)) (sym (dim[] B σ)) lB)

-- Every term of dimension ≤ 1 has a well-typed cylinder under Kω, for
-- every valid datum, with no hypothesis.
cylω-low : ∀ {D Γ Δ t A} → Hyp.ValidD Kω D Γ Δ → Γ ⊢tm t ∶ A → T (dim A <ℕ 2) →
           T (Cyl.touched Kω D t) → Δ ⊢tm Cyl.cyl Kω D t ∶ Cyl.cylTy Kω D t A
cylω-low V dt p q = cylω-wf V dt (low-h dt p) q
