------------------------------------------------------------------------
-- The cylinder context Q↑Y is well formed, and its generic datum is
-- valid (ledger C1d, item 3).
--
--   cylCtx-ok : Q ⊢ctx → GoodCtx Q → lenSel Y ≡ len Q → UpSel Q Y →
--               cylCtx Q Y ⊢ctx  ×  ValidD (gen Y) Q (cylCtx Q Y)
--
-- for every context Q (pasting or not) and every up-closed selection
-- Y, relative to a typed filler family on the coherences in the
-- boundaries of Q's types (`GoodCtx`). When those boundaries are
-- variables, as in every pasting context, `GoodCtx` holds for any
-- `Good`, in particular for `Good = λ _ _ → ⊥`, whose FillerOK is
-- trivial (module `VarBd`; `chain-good` for chains): no filler is needed.
--
-- The proof is by induction on Q. The new entries for x : A are
-- x⁻ : A[genMm Y] and, when x is selected, x⁺ : A[genMp Y] and
-- x↑ : a_x → b_x, which is well formed by CaTTExp.Naturality.Boundary
-- (cylTy-wf), the boundary cylinders being given by cyl-wf on Q↑Y and
-- moved to the extended context by `Restrict`: on the variables of Q,
-- the data gen (Y ◂ b) and gen Y have the same cylinders.
------------------------------------------------------------------------
module CaTTExp.Naturality.CylCtx where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PureMetatheory using (closed; tm[]; ty[])
open import CaTTExp.Weakening ∅ cattSide using (wk-tm; wk-sub; wk-ty; lookup-top; lookup-wk)
open import CaTTExp.GrayCtx.NaturalWF using (<-suc; n<sn; <→≢)
open import CaTTExp.Derived using (idS; id-tm; id-ty; lenₛ-renS; lookup-renS; lk-ext; lk-top; lk-skip; tm-ty; subst₂)
open import CaTTExp.DerivedBoundary using (idS∘)
open import CaTTExp.Naturality.Raw
open import CaTTExp.GraphFillerTotal.Chains using (chainC)
open import CaTTExp.Naturality.Commute using (module Laws; Scoped; ∨-false; anyL-ext; anyL-ext-ty; if-t; if-f)
open import CaTTExp.Naturality.Typing using (UpSel; module Hyp; module Gen; module Main)
open import CaTTExp.Naturality.Boundary using (BaseD; module Typed; ==-refl; Cmp; top; low; cmp)

------------------------------------------------------------------------
-- Small facts.

private
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  ⊥-T : ∀ {A : Set} {b} → b ≡ false → T b → A
  ⊥-T {b = true} () _
  ⊥-T {b = false} _ ()

selAt-here : ∀ Y c m → lenSel Y ≡ m → selAt (Y ◂ c) m ≡ c
selAt-here Y c .(lenSel Y) refl = if-t (==-refl (lenSel Y))

selAt-low : ∀ Y c i → T (i <ℕ lenSel Y) → selAt (Y ◂ c) i ≡ selAt Y i
selAt-low Y c i p = if-f (<→≢ i (lenSel Y) p)

------------------------------------------------------------------------
-- gen (Y ◂ c) agrees with gen Y on the variables of Y's context.

module Restrict (K : Filler) (Y : Sel) (c : Bool) where
  open Cyl K
  open Laws K
  open Gen K

  private
    n = lenSel Y
    G = gen (Y ◂ c)
    lI : lenₛ (idS n) ≡ n
    lI = lenₛ-renS n (λ i → i)
    toN : ∀ {i} m → lenₛ m ≡ n → T (i <ℕ n) → T (i <ℕ lenₛ m)
    toN m e p = subst (λ k → T (_ <ℕ k)) (sym e) p

  genMm-low : ∀ i → T (i <ℕ n) → lookupₛ (genMm (Y ◂ c)) i ≡ lookupₛ (genMm Y) i
  genMm-low i p = lk-ext (genMm Y) _ i (toN (genMm Y) (len-genMm Y) p)

  genMp-low : ∀ i → T (i <ℕ n) → lookupₛ (genMp (Y ◂ c)) i ≡ lookupₛ (genMp Y) i
  genMp-low i p = go c
    where
    go : ∀ c' → lookupₛ (genMp (Y ◂ c')) i ≡ lookupₛ (genMp Y) i
    go true  = lk-ext (genMp Y) _ i (toN (genMp Y) (len-genMp Y) p)
    go false = lk-ext (genMp Y) _ i (toN (genMp Y) (len-genMp Y) p)

  genTh-low : ∀ i → T (i <ℕ n) → lookupₛ (genTh (Y ◂ c)) i ≡ lookupₛ (genTh Y) i
  genTh-low i p = lk-ext (genTh Y) _ i (toN (genTh Y) (len-genTh Y) p)

  private
    D' = pre (idS n) G

    emm : idS n ∘ genMm (Y ◂ c) ≡ genMm Y
    emm = subst (λ m → idS m ∘ genMm (Y ◂ c) ≡ genMm Y) (len-genMm Y)
            (idS∘ (genMm Y) (genMm (Y ◂ c)) (λ i p → genMm-low i (subst (λ k → T (i <ℕ k)) (len-genMm Y) p)))

    emp : idS n ∘ genMp (Y ◂ c) ≡ genMp Y
    emp = subst (λ m → idS m ∘ genMp (Y ◂ c) ≡ genMp Y) (len-genMp Y)
            (idS∘ (genMp Y) (genMp (Y ◂ c)) (λ i p → genMp-low i (subst (λ k → T (i <ℕ k)) (len-genMp Y) p)))

    esel : ∀ i → T (i <ℕ n) → sel D' i ≡ sel (gen Y) i
    esel i p = trans (cong (touched G) (lookup-renS n (λ i → i) i p))
                     (trans (∨-false (selAt (Y ◂ c) i)) (selAt-low Y c i p))

    eth : ∀ i → T (i <ℕ n) → T (sel D' i) → th D' i ≡ th (gen Y) i
    eth i p _ = trans (cong (cyl G) (lookup-renS n (λ i → i) i p)) (genTh-low i p)

  module E = Ext D' (gen Y) n emm emp esel eth

  r-touched : ∀ t → ScTm n t → touched G t ≡ touched (gen Y) t
  r-touched t st = fst (anyL-ext (selAt (Y ◂ c)) (selAt Y) (selAt-low Y c)) t st

  r-cylTy : ∀ t A → ScTm n t → ScTy n A → cylTy G t A ≡ cylTy (gen Y) t A
  r-cylTy t A st sA =
    trans (sym (cong₂ (cylTy G) (id-tm n t st) (id-ty n A sA)))
    (trans (cylTy-pre G (idS n) t A (subst (λ m → ScTm m t) (sym lI) st) (subst (λ m → ScTy m A) (sym lI) sA))
           (E.cylTy-ext t A sA))

  r-cyl : ∀ t → ScTm n t → T (touched (gen Y) t) → cyl G t ≡ cyl (gen Y) t
  r-cyl t st p =
    trans (sym (cong (cyl G) (id-tm n t st)))
    (trans (cyl-pre G (idS n) t (subst (λ m → ScTm m t) (sym lI) st))
           (E.cyl-ext t st (subst T (sym (E.touched-ext t st)) p)))

------------------------------------------------------------------------
-- The theorem.

module CW (K : Filler) (Ksc : Scoped K) (Good : Ctx → Ty → Set) (ok : Hyp.FillerOK K Good) where
  open Cyl K
  open Laws K
  open Gen K
  open Hyp K
  open Main K Ksc Good ok
  open Typed K

  -- The coherences in the boundaries of the types of a context.
  GoodTy : Ty → Set
  GoodTy ⋆           = ⊤
  GoodTy (arr A s u) = GoodTy A × AllGood Good s × AllGood Good u

  GoodCtx : Ctx → Set
  GoodCtx ε       = ⊤
  GoodCtx (Q ▸ A) = GoodCtx Q × GoodTy A

  toBase : ∀ {D Γ Δ} → ValidD D Γ Δ → BaseD D Γ Δ
  toBase V = record { bmm = vmm ; bmp = vmp ; bsame = vsame ; bup = vup }
    where open ValidD V

  bd-from : ∀ {D Γ Δ} → ValidD D Γ Δ → ∀ A → Γ ⊢ty A → GoodTy A → CylBd D Δ A
  bd-from V ⋆           _              _            = tt
  bd-from V (arr A s u) (arr-wf ds du) (gA , gs , gu) =
    bd-from V A (tm-ty ds) gA , cyl-wf V ds gs , cyl-wf V du gu

  len-cylCtx : ∀ Q Y → lenSel Y ≡ len Q → len (cylCtx Q Y) ≡ cnt Y
  len-cylCtx ε       ◇           _ = refl
  len-cylCtx ε       (Y ◂ b)     ()
  len-cylCtx (Q ▸ A) ◇           ()
  len-cylCtx (Q ▸ A) (Y ◂ true)  e = cong (λ m → suc (suc (suc m))) (len-cylCtx Q Y (suc-inj e))
  len-cylCtx (Q ▸ A) (Y ◂ false) e = cong suc (len-cylCtx Q Y (suc-inj e))

  -- An up-closed selection restricts to the prefix.
  upQ : ∀ Q A Y b → Q ⊢ctx → lenSel Y ≡ len Q → UpSel (Q ▸ A) (Y ◂ b) → UpSel Q Y
  upQ Q A Y b wQ eQ up q B lq sq =
    trans (sym (anyL-ext-ty (selAt (Y ◂ b)) (selAt Y) (selAt-low Y b) B scB'))
          (up q B (trans (lk-skip Q A q ql) lq) (trans (selAt-low Y b q ql') sq))
    where
    cl = Sb.ctx-lookup closed wQ lq
    ql = fst cl
    ql' = subst (λ m → T (q <ℕ m)) (sym eQ) ql
    scB' = subst (λ m → ScTy m B) (sym eQ) (snd cl)

  -- One step of the induction: the context Q ▸ A.
  module Step (Q : Ctx) (A : Ty) (Y : Sel) (wQ : Q ⊢ctx) (wA : Q ⊢ty A) (gA : GoodTy A)
              (eQ : lenSel Y ≡ len Q) (IH : (cylCtx Q Y ⊢ctx) × ValidD (gen Y) Q (cylCtx Q Y)) where
    private
      n = lenSel Y
      Δ' = cylCtx Q Y
      wΔ' = fst IH
      V' = snd IH
      sA : ScTy (len Q) A
      sA = Sb.ty-sc closed wA
      sAn : ScTy n A
      sAn = subst (λ m → ScTy m A) (sym eQ) sA
      lΔ' : len Δ' ≡ cnt Y
      lΔ' = len-cylCtx Q Y eQ
      wQA : (Q ▸ A) ⊢ctx
      wQA = ▸-wf wQ wA
    open ValidD V' renaming (vmm to vmm'; vmp to vmp'; vth to vth'; vsame to vsame'; vup to vup')

    private
      toN : ∀ {i} → T (i <ℕ len Q) → T (i <ℕ n)
      toN p = subst (λ m → T (_ <ℕ m)) (sym eQ) p

      lkA : ∀ {B} x → lookup (Q ▸ A) x ≡ just B → x ≡ len Q → B ≡ A
      lkA {B} .(len Q) lx refl = sym (just-inj (trans (sym (lookup-top Q A)) lx))

      lkQ : ∀ {B} x → lookup (Q ▸ A) x ≡ just B → T (x <ℕ len Q) → lookup Q x ≡ just B
      lkQ x lx q = trans (sym (lk-skip Q A x q)) lx

      lk-genMm : ∀ b → lookupₛ (genMm (Y ◂ b)) (len Q) ≡ var (cnt Y)
      lk-genMm b = subst (λ m → lookupₛ (genMm (Y ◂ b)) m ≡ var (cnt Y)) (trans (len-genMm Y) eQ) (lk-top (genMm Y) _)

      lk-genTh : ∀ b → lookupₛ (genTh (Y ◂ b)) (len Q) ≡ var (suc (suc (cnt Y)))
      lk-genTh b = subst (λ m → lookupₛ (genTh (Y ◂ b)) m ≡ var (suc (suc (cnt Y)))) (trans (len-genTh Y) eQ)
                     (lk-top (genTh Y) _)

      -- A selected variable of Q: its cylinder, moved along a weakening.
      th-low : ∀ b {Δ} → (∀ {t B} → Δ' ⊢tm t ∶ B → Δ ⊢tm t ∶ B) →
               ∀ x B → lookup (Q ▸ A) x ≡ just B → T (selAt (Y ◂ b) x) → T (x <ℕ len Q) →
               Δ ⊢tm lookupₛ (genTh (Y ◂ b)) x ∶ cylTy (gen (Y ◂ b)) (var x) B
      th-low b {Δ} wk x B lx sx q =
        subst₂ (Δ ⊢tm_∶_) (sym (R.genTh-low x (toN q))) (sym (R.r-cylTy (var x) B (toN q) scB))
          (wk (vth' x B (lkQ x lx q) (subst T (selAt-low Y b x (toN q)) sx)))
        where
        module R = Restrict K Y b
        scB = subst (λ m → ScTy m B) (sym eQ) (snd (Sb.ctx-lookup closed wQ (lkQ x lx q)))

      same-low : ∀ b x → T (x <ℕ len Q) → selAt (Y ◂ b) x ≡ false →
                 lookupₛ (genMm (Y ◂ b)) x ≡ lookupₛ (genMp (Y ◂ b)) x
      same-low b x q sx =
        trans (R.genMm-low x (toN q))
        (trans (vsame' x q (trans (sym (selAt-low Y b x (toN q))) sx)) (sym (R.genMp-low x (toN q))))
        where module R = Restrict K Y b

    -- x unselected: Q↑Y ▸ A[genMm Y].
    stepF : UpSel (Q ▸ A) (Y ◂ false) →
            (cylCtx (Q ▸ A) (Y ◂ false) ⊢ctx) × ValidD (gen (Y ◂ false)) (Q ▸ A) (cylCtx (Q ▸ A) (Y ◂ false))
    stepF up = wΔ , record { vmm = vmm₁ ; vmp = vmp₁ ; vth = vth₁ ; vsame = vsame₁ ; vup = up }
      where
      A⁻ = A [ genMm Y ]ty
      Δ = Δ' ▸ A⁻
      wΔ : Δ ⊢ctx
      wΔ = ▸-wf wΔ' (ty[] wA vmm')
      lk⁻ : lookup Δ (cnt Y) ≡ just A⁻
      lk⁻ = subst (λ m → lookup Δ m ≡ just A⁻) lΔ' (lookup-top Δ' A⁻)
      uA : anyL (selAt Y) (fvTy A) ≡ false
      uA = trans (sym (anyL-ext-ty (selAt (Y ◂ false)) (selAt Y) (selAt-low Y false) A sAn))
                 (up (len Q) A (lookup-top Q A) (selAt-here Y false (len Q) eQ))
      sameA : A [ genMm Y ]ty ≡ A [ genMp Y ]ty
      sameA = same-ty (toBase V') A sA uA
      vmm₁ : Δ ⊢sub genMm (Y ◂ false) ∶ Q ▸ A
      vmm₁ = ,-wf (wk-sub vmm' wΔ) (var-wf wΔ lk⁻)
      vmp₁ : Δ ⊢sub genMp (Y ◂ false) ∶ Q ▸ A
      vmp₁ = ,-wf (wk-sub vmp' wΔ) (subst (Δ ⊢tm var (cnt Y) ∶_) sameA (var-wf wΔ lk⁻))
      vth₁ : ∀ x B → lookup (Q ▸ A) x ≡ just B → T (selAt (Y ◂ false) x) →
             Δ ⊢tm lookupₛ (genTh (Y ◂ false)) x ∶ cylTy (gen (Y ◂ false)) (var x) B
      vth₁ x B lx sx with cmp x (len Q) (fst (Sb.ctx-lookup closed wQA lx))
      ... | top refl = ⊥-T (selAt-here Y false (len Q) eQ) sx
      ... | low q    = th-low false (λ d → wk-tm d wΔ) x B lx sx q
      vsame₁ : ∀ x → T (x <ℕ len (Q ▸ A)) → selAt (Y ◂ false) x ≡ false →
               lookupₛ (genMm (Y ◂ false)) x ≡ lookupₛ (genMp (Y ◂ false)) x
      vsame₁ x p sx with cmp x (len Q) p
      ... | top refl = trans (lk-genMm false)
                         (sym (subst (λ m → lookupₛ (genMp (Y ◂ false)) m ≡ var (cnt Y)) (trans (len-genMp Y) eQ)
                                 (lk-top (genMp Y) _)))
      ... | low q    = same-low false x q sx

    -- x selected: Q↑Y ▸ A[genMm Y] ▸ A[genMp Y] ▸ (a_x → b_x).
    stepT : UpSel (Q ▸ A) (Y ◂ true) →
            (cylCtx (Q ▸ A) (Y ◂ true) ⊢ctx) × ValidD (gen (Y ◂ true)) (Q ▸ A) (cylCtx (Q ▸ A) (Y ◂ true))
    stepT up = wΔ , record { vmm = wk-sub bmm₂ wΔ ; vmp = wk-sub bmp₂ wΔ ; vth = vth₁ ; vsame = vsame₁ ; vup = up }
      where
      module R = Restrict K Y true
      A⁻ = A [ genMm Y ]ty
      A⁺ = A [ genMp Y ]ty
      Δ₁ = Δ' ▸ A⁻
      Δ₂ = Δ₁ ▸ A⁺
      C = cylTy (gen (Y ◂ true)) (var (len Q)) A
      Δ = Δ₂ ▸ C
      w₁ : Δ₁ ⊢ctx
      w₁ = ▸-wf wΔ' (ty[] wA vmm')
      w₂ : Δ₂ ⊢ctx
      w₂ = ▸-wf w₁ (wk-ty (ty[] wA vmp') w₁)
      lΔ₁ : len Δ₁ ≡ suc (cnt Y)
      lΔ₁ = cong suc lΔ'
      lk⁻ : lookup Δ₂ (cnt Y) ≡ just A⁻
      lk⁻ = lookup-wk Δ₁ (cnt Y) A⁺ (subst (λ m → lookup Δ₁ m ≡ just A⁻) lΔ' (lookup-top Δ' A⁻))
      lk⁺ : lookup Δ₂ (suc (cnt Y)) ≡ just A⁺
      lk⁺ = subst (λ m → lookup Δ₂ m ≡ just A⁺) lΔ₁ (lookup-top Δ₁ A⁺)
      bmm₂ : Δ₂ ⊢sub genMm (Y ◂ true) ∶ Q ▸ A
      bmm₂ = ,-wf (wk-sub (wk-sub vmm' w₁) w₂) (var-wf w₂ lk⁻)
      bmp₂ : Δ₂ ⊢sub genMp (Y ◂ true) ∶ Q ▸ A
      bmp₂ = ,-wf (wk-sub (wk-sub vmp' w₁) w₂) (var-wf w₂ lk⁺)
      bsame₂ : ∀ x → T (x <ℕ len (Q ▸ A)) → selAt (Y ◂ true) x ≡ false →
               lookupₛ (genMm (Y ◂ true)) x ≡ lookupₛ (genMp (Y ◂ true)) x
      bsame₂ x p sx with cmp x (len Q) p
      ... | top refl = ⊥-T sx (subst T (sym (selAt-here Y true (len Q) eQ)) tt)
      ... | low q    = same-low true x q sx
      B₂ : BaseD (gen (Y ◂ true)) (Q ▸ A) Δ₂
      B₂ = record { bmm = bmm₂ ; bmp = bmp₂ ; bsame = bsame₂ ; bup = up }

      -- The boundary cylinders of A, moved from Q↑Y to Δ₂.
      mv : ∀ t B → ScTm n t → ScTy n B → CylT (gen Y) Δ' t B → CylT (gen (Y ◂ true)) Δ₂ t B
      mv t B st sB h p =
        subst₂ (Δ₂ ⊢tm_∶_) (sym (R.r-cyl t st p')) (sym (R.r-cylTy t B st sB)) (wk-tm (wk-tm (h p') w₁) w₂)
        where p' = subst T (R.r-touched t st) p
      bd-move : ∀ B → ScTy n B → CylBd (gen Y) Δ' B → CylBd (gen (Y ◂ true)) Δ₂ B
      bd-move ⋆           _               _              = tt
      bd-move (arr B s u) (sB , ss , su) (bB , bs , bu) = bd-move B sB bB , mv s B ss sB bs , mv u B su sB bu

      wC : Δ₂ ⊢ty C
      wC = cylTy-wf B₂ (var-wf wQA (lookup-top Q A)) (bd-move A sAn (bd-from V' A wA gA))
      wΔ : Δ ⊢ctx
      wΔ = ▸-wf w₂ wC
      lΔ₂ : len Δ₂ ≡ suc (suc (cnt Y))
      lΔ₂ = cong suc lΔ₁

      vth₁ : ∀ x B → lookup (Q ▸ A) x ≡ just B → T (selAt (Y ◂ true) x) →
             Δ ⊢tm lookupₛ (genTh (Y ◂ true)) x ∶ cylTy (gen (Y ◂ true)) (var x) B
      vth₁ x B lx sx with cmp x (len Q) (fst (Sb.ctx-lookup closed wQA lx))
      ... | top refl =
        subst₂ (Δ ⊢tm_∶_) (sym (lk-genTh true)) (cong (cylTy (gen (Y ◂ true)) (var (len Q))) (sym (lkA (len Q) lx refl)))
          (var-wf wΔ (subst (λ m → lookup Δ m ≡ just C) lΔ₂ (lookup-top Δ₂ C)))
      ... | low q    = th-low true (λ d → wk-tm (wk-tm (wk-tm d w₁) w₂) wΔ) x B lx sx q
      vsame₁ : ∀ x → T (x <ℕ len (Q ▸ A)) → selAt (Y ◂ true) x ≡ false →
               lookupₛ (genMm (Y ◂ true)) x ≡ lookupₛ (genMp (Y ◂ true)) x
      vsame₁ = bsame₂

  cylCtx-ok : ∀ Q Y → Q ⊢ctx → GoodCtx Q → lenSel Y ≡ len Q → UpSel Q Y →
              (cylCtx Q Y ⊢ctx) × ValidD (gen Y) Q (cylCtx Q Y)
  cylCtx-ok ε ◇ _ _ _ _ =
    ε-wf , record { vmm = ⟨⟩-wf ε-wf ; vmp = ⟨⟩-wf ε-wf
                  ; vth = λ { x A () _ } ; vsame = λ { x () _ } ; vup = λ { x A () _ } }
  cylCtx-ok ε       (Y ◂ b) _ _ () _
  cylCtx-ok (Q ▸ A) ◇       _ _ () _
  cylCtx-ok (Q ▸ A) (Y ◂ true) (▸-wf wQ wA) (gQ , gA) e up =
    Step.stepT Q A Y wQ wA gA (suc-inj e) (cylCtx-ok Q Y wQ gQ (suc-inj e) (upQ Q A Y true wQ (suc-inj e) up)) up
  cylCtx-ok (Q ▸ A) (Y ◂ false) (▸-wf wQ wA) (gQ , gA) e up =
    Step.stepF Q A Y wQ wA gA (suc-inj e) (cylCtx-ok Q Y wQ gQ (suc-inj e) (upQ Q A Y false wQ (suc-inj e) up)) up

------------------------------------------------------------------------
-- Contexts whose types have variable boundaries (every pasting
-- context, in particular every chain): no filler is needed.

module VarBd (K : Filler) (Ksc : Scoped K) where
  Nope : Ctx → Ty → Set
  Nope _ _ = ⊥

  okNope : Hyp.FillerOK K Nope
  okNope _ _ _ _ _ _ _ ()

  open CW K Ksc Nope okNope public

  chain-good : ∀ m → GoodCtx (chainC m)
  chain-good zero    = tt , tt
  chain-good (suc m) = (chain-good m , tt) , tt , tt , tt
