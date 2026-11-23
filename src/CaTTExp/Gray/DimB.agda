------------------------------------------------------------------------
-- DimOK for two-tier L with binding formers (the hypothesis of
-- CaTTExp.Gray.MarksBSubst.Stable): a derivable coh of binder syntax is
-- at least as high as its pasting context,
--
--   Θ ⊢ps,  Θ ⊢ arr A t u,  graySideD Θ A t u  ⇒  dim Θ ≤ dim (arr A t u).
--
-- graySideD is L's side condition on the erasure (CaTTExp.Gray.DesSide:
-- a destructor erased to its cell argument). CohDim.dimOK-from gives
-- the bound from the ranks of the erased source's supports, and this
-- module bounds those ranks by induction on the binder-syntax
-- derivation (`supp-rank`, the counterpart of CohDim.supp-rank): an
-- erased former occurrence has the supports of its cell argument,
-- which is derivable at a dimension at most the occurrence's
-- (`CellDim`, an interface hypothesis: for DES the cell is an n-cell
-- and the result an n- or (n+1)-cell).
--
-- Derivations are those of the mark-free instance
-- (CaTTExp.Binder.Forget); presupposition `tm-ty` is a parameter until
-- the kernel provides it.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Embed
open import CaTTExp.Binder.Signature using () renaming (Signature to NSignature)
import CaTTExp.Binder.Forget
import CaTTExp.Binder.Pasting
import CaTTExp.Binder.SyntaxLemmas
import CaTTExp.Pure as P
import CaTTExp.Pasting

module CaTTExp.Gray.DimB
  (𝕊₀ : Old.Signature)
  (bi : Binders (Old.Signature.K 𝕊₀))
  (cellArg : Binders.B bi → Maybe Nat)
  where

private
  𝕊 : NSignature
  𝕊 = extend 𝕊₀ bi
module N = NSignature 𝕊

open Old.Signature 𝕊₀
open import CaTTExp.Pasting 𝕊₀ using (pss; pse; psd) renaming (_⊢ps_∶_ to _⊢ps₀_∶_)
open import CaTTExp.Gray.Support 𝕊₀
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊₀
open import CaTTExp.Gray.Graded 𝕊₀
open import CaTTExp.Gray.PsFacts 𝕊₀ using (PsFacts; ps-facts)
open import CaTTExp.Gray.Orient 𝕊₀ using (chainε-false)
open import CaTTExp.Gray.OrientRev 𝕊₀ using (path⇒)
open import CaTTExp.Gray.CohDim 𝕊₀ using (rk; ht; hgt-le; opDim; tops-len; nth-snoc-eq; nth-snoc-ne; module FRank; dimOK-from)
open import CaTTExp.Gray.DesSide 𝕊₀ bi cellArg using (graySideD; dTy; dTm; dCtx; dSub; dCell; dArg)
open CaTTExp.Binder.SyntaxLemmas (Old.Signature.K 𝕊₀) (Binders.B bi) using (len-openTel)

module Fg = CaTTExp.Binder.Forget 𝕊 graySideD
module F = Fg.F
private
  module BP = CaTTExp.Binder.Pasting 𝕊
  module PP = CaTTExp.Pasting P.∅

------------------------------------------------------------------------
-- Helpers.

private
  bind-just : ∀ {a b} {A : Set a} {Z : Set b} (m : Maybe A) (f : A → Maybe Z) {z} →
              (m >>= f) ≡ just z → Σ A λ x → (m ≡ just x) × (f x ≡ just z)
  bind-just (just x) f e = x , refl , e

  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  ⊎-case : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
  ⊎-case (inj₁ a) f g = f a
  ⊎-case (inj₂ b) f g = g b

  ∸1-mono : ∀ {a b} → a ≤ b → a ∸ 1 ≤ b ∸ 1
  ∸1-mono z≤n           = z≤n
  ∸1-mono (s≤s z≤n)     = z≤n
  ∸1-mono (s≤s (s≤s l)) = s≤s l

------------------------------------------------------------------------
-- Erasure preserves dimensions, lengths and lookups.

arr-erase : ∀ B s s' {A₀} → dTy (N.arr B s s') ≡ just A₀ →
            Σ Ty λ B₀ → Σ Tm λ s₀ → Σ Tm λ s'₀ →
              (dTy B ≡ just B₀) × (dTm s ≡ just s₀) × (dTm s' ≡ just s'₀) × (A₀ ≡ arr B₀ s₀ s'₀)
arr-erase B s s' e with bind-just (dTy B) _ e
... | B₀ , eB , e₁ with bind-just (dTm s) _ e₁
... | s₀ , es , e₂ with bind-just (dTm s') _ e₂
... | s'₀ , es' , refl = B₀ , s₀ , s'₀ , eB , es , es' , refl

dim-d : ∀ A {A₀} → dTy A ≡ just A₀ → dim A₀ ≡ N.dim A
dim-d N.⋆ refl = refl
dim-d (N.arr B s s') e with arr-erase B s s' e
... | B₀ , _ , _ , eB , _ , _ , refl = cong suc (dim-d B eB)

ctx-erase : ∀ Γ ms A {Γ₀} → dCtx (Γ N.▸[ ms ] A) ≡ just Γ₀ →
            Σ Ctx λ Γ₁ → Σ Ty λ A₀ → (dCtx Γ ≡ just Γ₁) × (dTy A ≡ just A₀) × (Γ₀ ≡ Γ₁ ▸ A₀)
ctx-erase Γ ms A e with bind-just (dCtx Γ) _ e
... | Γ₁ , eΓ , e₁ with bind-just (dTy A) _ e₁
... | A₀ , eA , refl = Γ₁ , A₀ , eΓ , eA , refl

sub-erase : ∀ σ t {σ₀} → dSub (σ N.,ₛ t) ≡ just σ₀ →
            Σ Sub λ σ₁ → Σ Tm λ t₀ → (dSub σ ≡ just σ₁) × (dTm t ≡ just t₀) × (σ₀ ≡ σ₁ ,ₛ t₀)
sub-erase σ t e with bind-just (dSub σ) _ e
... | σ₁ , eσ , e₁ with bind-just (dTm t) _ e₁
... | t₀ , et , refl = σ₁ , t₀ , eσ , et , refl

coh-erase : ∀ Δ A σ {t₀} → dTm (N.coh Δ A σ) ≡ just t₀ →
            Σ Ctx λ Δ₀ → Σ Ty λ A₀ → Σ Sub λ σ₀ →
              (dCtx Δ ≡ just Δ₀) × (dTy A ≡ just A₀) × (dSub σ ≡ just σ₀) × (t₀ ≡ coh Δ₀ A₀ σ₀)
coh-erase Δ A σ e with bind-just (dCtx Δ) _ e
... | Δ₀ , eΔ , e₁ with bind-just (dTy A) _ e₁
... | A₀ , eA , e₂ with bind-just (dSub σ) _ e₂
... | σ₀ , eσ , refl = Δ₀ , A₀ , σ₀ , eΔ , eA , eσ , refl

len-d : ∀ Γ {Γ₀} → dCtx Γ ≡ just Γ₀ → len Γ₀ ≡ N.len Γ
len-d N.ε refl = refl
len-d (Γ N.▸[ ms ] A) e with ctx-erase Γ ms A e
... | Γ₁ , _ , eΓ , _ , refl = cong suc (len-d Γ eΓ)

lenₛ-d : ∀ σ {σ₀} → dSub σ ≡ just σ₀ → lenₛ σ₀ ≡ N.lenₛ σ
lenₛ-d N.⟨⟩ refl = refl
lenₛ-d (σ N.,ₛ t) e with sub-erase σ t e
... | σ₁ , _ , eσ , _ , refl = cong suc (lenₛ-d σ eσ)

dimCtx-d : ∀ Γ {Γ₀} → dCtx Γ ≡ just Γ₀ → dimCtx Γ₀ ≡ N.dimCtx Γ
dimCtx-d N.ε refl = refl
dimCtx-d (Γ N.▸[ ms ] A) e with ctx-erase Γ ms A e
... | Γ₁ , A₀ , eΓ , eA , refl = cong₂ max (dim-d A eA) (dimCtx-d Γ eΓ)

lookup-d : ∀ Γ {Γ₀ i A} → dCtx Γ ≡ just Γ₀ → N.lookup Γ i ≡ just A →
           Σ Ty λ A₀ → (lookup Γ₀ i ≡ just A₀) × (dTy A ≡ just A₀)
lookup-d (Γ N.▸[ ms ] B) {i = i} e eq with ctx-erase Γ ms B e
... | Γ₁ , B₀ , eΓ , eB , refl rewrite len-d Γ eΓ with i ==ℕ N.len Γ
lookup-d (Γ N.▸[ ms ] B) e refl | Γ₁ , B₀ , eΓ , eB , refl | true  = B₀ , refl , eB
lookup-d (Γ N.▸[ ms ] B) e eq   | Γ₁ , B₀ , eΓ , eB , refl | false = lookup-d Γ eΓ eq

-- The side condition on binder syntax is L's on the erasure.
side-ok : ∀ Δ A t u → T (graySideD Δ A t u) →
          Σ Ctx λ Δ₀ → Σ Ty λ A₀ → Σ Tm λ t₀ → Σ Tm λ u₀ →
            (dCtx Δ ≡ just Δ₀) × (dTy A ≡ just A₀) × (dTm t ≡ just t₀) × (dTm u ≡ just u₀) ×
            T (graySide Δ₀ A₀ t₀ u₀)
side-ok Δ A t u ok with dCtx Δ | dTy A | dTm t | dTm u
... | just Δ₀ | just A₀ | just t₀ | just u₀ = Δ₀ , A₀ , t₀ , u₀ , refl , refl , refl , refl , ok

dim-op : ∀ d ts A → N.dim (N.opTy d ts A) ≡ N.dim A
dim-op d ts N.⋆           = refl
dim-op d ts (N.arr A _ _) = cong suc (dim-op d ts A)

dim-[] : ∀ A σ → N.dim (A N.[ σ ]ty) ≡ N.dim A
dim-[] N.⋆           σ = refl
dim-[] (N.arr A _ _) σ = cong suc (dim-[] A σ)

private
  sub-len : ∀ {Γ σ Δ} → Γ F.⊢sub σ ∶ Δ → N.lenₛ σ ≡ N.len Δ
  sub-len (F.⟨⟩-wf _)    = refl
  sub-len (F.,-wf s _ _) = cong suc (sub-len s)

  args-len : ∀ {Γ ts Θ} → Γ F.⊢args ts ∶ Θ → N.lenₛ ts ≡ N.len Θ
  args-len (F.⟨⟩-a _)    = refl
  args-len (F.,-a a _ _) = cong suc (args-len a)

------------------------------------------------------------------------
-- The cell argument of a destructor is derivable at a dimension at most
-- the occurrence's.

CellDim : Set
CellDim = ∀ b y Θ j C → cellArg b ≡ just j → T (N.bside b y Θ) →
          N.lookup (N.bargs b y Θ) j ≡ just C → N.dim C ≤ N.dim (N.bres b y Θ)

------------------------------------------------------------------------
-- Support ranks of derivable terms, after erasure.

module _ (cellDim : CellDim) (tm-ty : ∀ {Γ t A} → Γ F.⊢tm t ∶ A → Γ F.⊢ty A) where

  mutual
    supp-rank : ∀ {Γ Γ₀ t A t₀} → Γ F.⊢tm t ∶ A → dCtx Γ ≡ just Γ₀ → dTm t ≡ just t₀ →
                ∀ {x} → x ∈L topS t₀ → rk Γ₀ x ≤ N.dim A ∸ 1
    supp-rank {Γ} {Γ₀} {A = A} (F.var-wf {i} w eL) eΓ refl (here refl) with lookup-d Γ eΓ eL
    ... | C₀ , eL₀ , eC =
      subst (_≤ N.dim A ∸ 1) (sym (+-zero (ht Γ₀ i)))
        (subst (λ n → ht Γ₀ i ≤ n ∸ 1) (dim-d A eC) (hgt-le Γ₀ i eL₀))
    supp-rank (F.var-wf w eL) eΓ refl (there ())
    supp-rank (F.cst-wf w v) eΓ refl ()
    supp-rank {Γ} {Γ₀} (F.coh-wf {Δ} {B} {s} {s'} {σ} _ _ _ ok sσ) eΓ e {x} mx
      with side-ok Δ B s s' ok | coh-erase Δ (N.arr B s s') σ e
    ... | Δ₀ , B₀ , s₀ , s'₀ , eΔ , eB , es , es' , side | Δ₁ , A₁ , σ₀ , eΔ₁ , eA₁ , eσ , refl
      with just-inj (trans (sym eΔ₁) eΔ) | arr-erase B s s' eA₁
    ... | refl | B₁ , s₁ , s'₁ , eB₁ , es₁ , es'₁ , refl
      with just-inj (trans (sym eB₁) eB) | just-inj (trans (sym es₁) es) | just-inj (trans (sym es'₁) es')
    ... | refl | refl | refl
      rewrite dim-[] B σ | sym (dim-d B eB) = coh-case side mx
      where
      coh-case : T (graySide Δ₀ B₀ s₀ s'₀) → x ∈L topS (coh Δ₀ (arr B₀ s₀ s'₀) σ₀) → rk Γ₀ x ≤ dim B₀
      coh-case side′ mx′ with cohCase Δ₀ B₀ s₀ s'₀
      ... | true = ⊥-elim (none mx′)
        where
        none : x ∈L [] → ⊥
        none ()
      ... | false
        with any-witness (any-cm⁻ (Ftuple (topsSub σ₀)) (topT (homs Δ₀))
                           (subst (Any _) (cm≡ (Ftuple (topsSub σ₀)) (topT (homs Δ₀))) mx′))
      ...   | c , mc , mxc
        with path⇒ (λ _ → false) (homs Δ₀) true (dimK (homs Δ₀))
               (subst (λ L → c ∈L L) (sym (chainε-false true (dimK (homs Δ₀)) (homs Δ₀))) mc)
      ...   | is , _ , p =
        ≤-trans (FRank.F-rank Γ₀ Δ₀ (topsSub σ₀) (sub-bnd sσ eΓ eΔ eσ) (Ranks.homs-ok Δ₀) p mxc)
          (subst (_≤ dim B₀) (sym (Ranks.chain-rank Δ₀ true (dimK (homs Δ₀)) mc)) (opDim Δ₀ B₀ s₀ s'₀ side′))
    supp-rank {Γ} {Γ₀} (F.bnd-wf {b} {y} {Θ} {ts} _ _ _ ok as) eΓ e mx =
      cell (cellArg b) refl e mx
      where
      cell : ∀ c → cellArg b ≡ c → ∀ {t₀} → dCell c ts ≡ just t₀ →
             ∀ {x} → x ∈L topS t₀ → rk Γ₀ x ≤ N.dim (N.opTy 0 ts (N.bres b y Θ)) ∸ 1
      cell nothing  ec ()
      cell (just j) ec e′ mx′ with args-rank as eΓ e′ mx′
      ... | C , eC , le =
        ≤-trans le (subst (λ n → N.dim C ∸ 1 ≤ n ∸ 1) (sym (dim-op 0 ts (N.bres b y Θ)))
                      (∸1-mono (cellDim b y Θ j C ec ok eC)))

    -- The images of a substitution's variables.
    sub-bnd : ∀ {Γ Γ₀ σ Δ Δ₀ σ₀} → Γ F.⊢sub σ ∶ Δ → dCtx Γ ≡ just Γ₀ → dCtx Δ ≡ just Δ₀ →
              dSub σ ≡ just σ₀ → ∀ {w C} → lookup Δ₀ w ≡ just C →
              ∀ {y} → y ∈L nth w (topsSub σ₀) → rk Γ₀ y ≤ dim C ∸ 1
    sub-bnd (F.⟨⟩-wf _) eΓ refl refl () _
    sub-bnd {Γ₀ = Γ₀} (F.,-wf {σ} {Δ} {t} {ms} {A} sd d _) eΓ eΔ eσ {w} eL my
      with ctx-erase Δ ms A eΔ | sub-erase σ t eσ
    ... | Δ₁ , A₀ , eΔ₁ , eA , refl | σ₁ , t₀ , eσ₁ , et , refl with w ==ℕ len Δ₁ in q
    sub-bnd {Γ₀ = Γ₀} (F.,-wf {σ} {Δ} {t} {ms} {A} sd d _) eΓ eΔ eσ {w} refl {y} my
      | Δ₁ , A₀ , eΔ₁ , eA , refl | σ₁ , t₀ , eσ₁ , et , refl | true =
      subst (λ n → rk Γ₀ y ≤ n ∸ 1) (trans (dim-[] A σ) (sym (dim-d A eA)))
        (supp-rank d eΓ et (subst (λ L → _ ∈L L) eq my))
      where
      lenq : len Δ₁ ≡ length (topsSub σ₁)
      lenq = trans (len-d Δ eΔ₁) (trans (sym (sub-len sd)) (trans (sym (lenₛ-d σ eσ₁)) (sym (tops-len σ₁))))
      eq : nth w (topsSub σ₁ ++ topS t₀ ∷ []) ≡ topS t₀
      eq rewrite ==ℕ-sound w (len Δ₁) (subst T (sym q) tt) | lenq = nth-snoc-eq (topsSub σ₁) (topS t₀)
    ... | false = sub-bnd sd eΓ eΔ₁ eσ₁ eL (subst (λ L → _ ∈L L) eq my)
      where
      lenq : len Δ₁ ≡ length (topsSub σ₁)
      lenq = trans (len-d Δ eΔ₁) (trans (sym (sub-len sd)) (trans (sym (lenₛ-d σ eσ₁)) (sym (tops-len σ₁))))
      eq : nth w (topsSub σ₁ ++ topS t₀ ∷ []) ≡ nth w (topsSub σ₁)
      eq = nth-snoc-ne (topsSub σ₁) (topS t₀) w (trans (cong (w ==ℕ_) (sym lenq)) q)

    -- The cell argument among a binder's arguments.
    args-rank : ∀ {Γ Γ₀ ts Θ j t₀} → Γ F.⊢args ts ∶ Θ → dCtx Γ ≡ just Γ₀ → dArg j ts ≡ just t₀ →
                ∀ {x} → x ∈L topS t₀ → Σ N.Ty λ C → (N.lookup Θ j ≡ just C) × (rk Γ₀ x ≤ N.dim C ∸ 1)
    args-rank (F.⟨⟩-a _) eΓ () mx
    args-rank {j = j} (F.,-a {ts} {Θ} {t} {ms} {A} a d _) eΓ e mx with j ==ℕ N.lenₛ ts in q
    ... | true  = A , look , subst (λ n → _ ≤ n ∸ 1) (dim-op 0 ts A) (supp-rank d eΓ e mx)
      where
      look : N.lookup (Θ N.▸[ ms ] A) j ≡ just A
      look rewrite trans (cong (j ==ℕ_) (sym (args-len a))) q = refl
    ... | false with args-rank a eΓ e mx
    ...   | C , eC , le = C , look , le
      where
      look : N.lookup (Θ N.▸[ ms ] A) j ≡ just C
      look rewrite trans (cong (j ==ℕ_) (sym (args-len a))) q = eC

  -- The supports in a type, and in supp t A.
  suppTy-rank : ∀ {Γ Γ₀} A {A₀} → Γ F.⊢ty A → dCtx Γ ≡ just Γ₀ → dTy A ≡ just A₀ →
                ∀ {x} → x ∈L suppTy A₀ → rk Γ₀ x ≤ N.dim A ∸ 1
  suppTy-rank N.⋆ _ eΓ refl ()
  suppTy-rank (N.arr B s s') d eΓ eA mx with arr-erase B s s' eA
  suppTy-rank (N.arr N.⋆ s s') d eΓ eA () | B₀ , s₀ , s'₀ , refl , _ , _ , refl
  suppTy-rank (N.arr (N.arr B c c') s s') (F.arr-wf ds ds') eΓ eA mx | B₀ , s₀ , s'₀ , eB , es , es' , refl
    with arr-erase B c c' eB
  ... | B₁ , c₀ , c'₀ , eB₁ , ec , ec' , refl =
    ⊎-case (any-++⁻ (suppTy (arr B₁ c₀ c'₀)) mx)
      (λ m → ≤-step (suppTy-rank (N.arr B c c') (tm-ty ds) eΓ eB m))
      (λ m → ⊎-case (any-++⁻ (topS s₀) m)
               (λ m' → ≤-step (supp-rank ds eΓ es m'))
               (λ m' → ≤-step (supp-rank ds' eΓ es' m')))

  supp-all : ∀ {Γ Γ₀ t A t₀ A₀} → Γ F.⊢tm t ∶ A → dCtx Γ ≡ just Γ₀ → dTm t ≡ just t₀ → dTy A ≡ just A₀ →
             ∀ {x} → x ∈L supp t₀ A₀ → rk Γ₀ x ≤ dim A₀ ∸ 1
  supp-all {A = A} {t₀} d eΓ et eA mx rewrite dim-d A eA with any-++⁻ (topS t₀) mx
  ... | inj₁ m = supp-rank d eΓ et m
  ... | inj₂ m = suppTy-rank A (tm-ty d) eΓ eA m

------------------------------------------------------------------------
-- Pasting contexts: the pure context's image in 𝕊₀.

open import CaTTExp.Gray.SupportIota 𝕊₀ using (ιTy; ιTm; ιCtx; ιSub; len-ι)

mutual
  dι-ty : ∀ A → dTy (BP.embTy A) ≡ just (ιTy A)
  dι-ty P.⋆ = refl
  dι-ty (P.arr A t u) rewrite dι-ty A | dι-tm t | dι-tm u = refl

  dι-tm : ∀ t → dTm (BP.embTm t) ≡ just (ιTm t)
  dι-tm (P.var i) = refl
  dι-tm (P.coh Γ A σ) rewrite dι-ctx Γ | dι-ty A | dι-sub σ = refl
  dι-tm (P.cst ())

  dι-ctx : ∀ Γ → dCtx (BP.embCtx Γ) ≡ just (ιCtx Γ)
  dι-ctx P.ε = refl
  dι-ctx (Γ P.▸ A) rewrite dι-ctx Γ | dι-ty A = refl

  dι-sub : ∀ σ → dSub (BP.embSub σ) ≡ just (ιSub σ)
  dι-sub P.⟨⟩ = refl
  dι-sub (σ P.,ₛ t) rewrite dι-sub σ | dι-tm t = refl

private
  ps-ι : ∀ {Γ x A} → Γ PP.⊢ps x ∶ A → ιCtx Γ ⊢ps₀ x ∶ ιTy A
  ps-ι PP.pss = pss
  ps-ι (PP.pse {Γ} {x} {A} d) with pse (ps-ι d)
  ... | r rewrite len-ι Γ = r
  ps-ι (PP.psd d) = psd (ps-ι d)

------------------------------------------------------------------------
-- DimOK.

module _ (cellDim : CellDim) (tm-ty : ∀ {Γ t A} → Γ F.⊢tm t ∶ A → Γ F.⊢ty A) where

  dimOK : ∀ {Θ A t u} → Θ BP.⊢ps → Θ F.⊢ty N.arr A t u → T (graySideD Θ A t u) →
          N.dimCtx Θ ≤ suc (N.dim A)
  dimOK {Θ} {A} {t} {u} (Θp , eP , PP.ps d) (F.arr-wf dt du) ok with side-ok Θ A t u ok
  ... | Θ₀ , A₀ , t₀ , u₀ , eΘ , eA , et , eu , side
    with just-inj (trans (sym eΘ) (subst (λ X → dCtx X ≡ just (ιCtx Θp)) (BP.toPure-sound Θ eP) (dι-ctx Θp)))
  ... | refl =
    subst (λ a → a ≤ suc (N.dim A)) (dimCtx-d Θ eΘ) (subst (λ b → dimCtx Θ₀ ≤ suc b) (dim-d A eA)
      (dimOK-from (fst (ps-facts (ps-ι d))) side (supp-all cellDim tm-ty dt eΘ et eA)))
