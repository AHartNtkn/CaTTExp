------------------------------------------------------------------------
-- Presupposition for ⟦Γ⟧, ⊤ and the generic diagram η_Γ (ledger S26k
-- step 2), in the kernel with plain CaTT's side condition and rule
-- (MARK):
--
--   Θ ⊢ ⋆                                         (⟦Γ⟧, ⊤)
--   Θ ⊢ (ΣA_j)[⊤, ⟦Γ⟧, η_{Γ,0}, …, η_{Γ,j−1}]      (η_{Γ,j})
--
-- for every context Θ and every valid head. The proof is LimPresup's
-- for the cone legs, with ΣΓ in place of the cone context: by
-- induction on j, the substitution (⊤, ⟦Γ⟧, η_{Γ,0}, …, η_{Γ,j−1}) is
-- well typed into ΣΓ's first 2 + j entries (`gen-sub`), each η typed
-- by its binder rule once the earlier ones are (its side condition's
-- closedness holds because its type is well formed in ε), and then
-- ΣA_j, well formed over those entries by pure CaTT's suspension
-- (`PureMetatheory.Σty-wf`, embedded by `PureEmbed`), is well formed
-- by substitution. ⟦Γ⟧ is typed by its own binder rule, its telescope
-- being Γ itself. Everything is typed in ε and weakened to Θ (the
-- heads are closed).
--
-- Hence PresupLaws (`gen-presup`) and `gen-tm-ty`: every term of CaTT
-- with ⟦Γ⟧, ⊤ and η has a well-formed type.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
open import CaTTExp.Binder.GenHeads
open import CaTTExp.Binder.FreeObj using (free)
open import CaTTExp.Binder.LimHeads using (module PureEmb)
import CaTTExp.Binder.GenHeadsLaws as GL
import CaTTExp.Binder.Laws as BL
open import CaTTExp.PureMetatheory using (Σty-wf; Σctx-wf)
open import CaTTExp.Suspension P.∅ using (Σty; Σctx)

module CaTTExp.Binder.GenHeadsPresup where

open GL P.∅ using (𝕊; genLaws)
open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.TypingWith 𝕊 cattSide varMark
open import CaTTExp.Binder.Scoping 𝕊 cattSide varMark using (ty-sc; sub-lc)
open import CaTTExp.Binder.VarMark 𝕊 cattSide using (markRen; markSub; markVar)
open import CaTTExp.Binder.Rename 𝕊 cattSide varMark using (wk-ty)
open import CaTTExp.Binder.Subst 𝕊 cattSide varMark using (ty[])
open import CaTTExp.Binder.PureSide 𝕊 using (cattSide-pure)
open import CaTTExp.Binder.PureEmbed 𝕊 cattSide varMark using (SidePure; ctx-emb; ty-emb)
open import CaTTExp.Binder.Presup 𝕊 cattSide varMark using (PresupLaws; tm-ty)
open import CaTTExp.Binder.Close K B using (clTy; clTm; clTel; clSub; sc-clTel)
open import CaTTExp.Binder.HonestHeads 𝕊 using (Honest; module Typed)
open Typed cattSide varMark using (open-cl-id)
open GenConstruction K B (λ b → b)
open PureEmb K B
open BL 𝕊 using (Closed; BinderLaws)

closed : Closed
closed ()

laws : BinderLaws
laws = genLaws

------------------------------------------------------------------------
-- The pure embedding (as in LimPresup).

sp : SidePure
sp Δ A t u p = subst T (sym (cattSide-pure Δ A t u)) p

mutual
  pe-ty : ∀ A → peTy A ≡ embTy A
  pe-ty P.⋆           = refl
  pe-ty (P.arr A t u) rewrite pe-ty A | pe-tm t | pe-tm u = refl

  pe-tm : ∀ t → peTm t ≡ embTm t
  pe-tm (P.var i)     = refl
  pe-tm (P.coh Θ A τ) rewrite pe-ctx Θ | pe-ty A | pe-sub τ = refl
  pe-tm (P.cst ())

  pe-ctx : ∀ Γ → peCtx Γ ≡ embCtx Γ
  pe-ctx P.ε       = refl
  pe-ctx (Γ P.▸ A) rewrite pe-ctx Γ | pe-ty A = refl

  pe-sub : ∀ σ → peSub σ ≡ embSub σ
  pe-sub P.⟨⟩       = refl
  pe-sub (σ P.,ₛ t) rewrite pe-sub σ | pe-tm t = refl

mutual
  lc-peTy : ∀ d A → T (lcTy? d (peTy A))
  lc-peTy d P.⋆           = tt
  lc-peTy d (P.arr A t u) = ∧T (lc-peTy d A) (∧T (lc-peTm d t) (lc-peTm d u))

  lc-peTm : ∀ d t → T (lcTm? d (peTm t))
  lc-peTm d (P.var i)     = tt
  lc-peTm d (P.coh Θ A τ) = lc-peSub d τ
  lc-peTm d (P.cst ())

  lc-peSub : ∀ d σ → T (lcSub? d (peSub σ))
  lc-peSub d P.⟨⟩       = tt
  lc-peSub d (σ P.,ₛ t) = ∧T (lc-peSub d σ) (lc-peTm d t)

pe-ctx-wf : ∀ {Γ} → Γ P.⊢ctx → peCtx Γ ⊢ctx
pe-ctx-wf {Γ} w = subst _⊢ctx (sym (pe-ctx Γ)) (ctx-emb sp w)

pe-ty-wf : ∀ {Γ A} → Γ P.⊢ty A → peCtx Γ ⊢ty peTy A
pe-ty-wf {Γ} {A} a rewrite pe-ctx Γ | pe-ty A = ty-emb sp a

------------------------------------------------------------------------
-- Closing an embedded context: locally closed at depth 1, and honest.

mutual
  lc-clTy : ∀ A → T (lcTy? 1 (clTy 0 (peTy A)))
  lc-clTy P.⋆           = tt
  lc-clTy (P.arr A t u) = ∧T (lc-clTy A) (∧T (lc-clTm t) (lc-clTm u))

  lc-clTm : ∀ t → T (lcTm? 1 (clTm 0 (peTm t)))
  lc-clTm (P.var i)     = tt
  lc-clTm (P.coh Θ A τ) = lc-clSub τ
  lc-clTm (P.cst ())

  lc-clSub : ∀ σ → T (lcSub? 1 (clSub 0 (peSub σ)))
  lc-clSub P.⟨⟩       = tt
  lc-clSub (σ P.,ₛ t) = ∧T (lc-clSub σ) (lc-clTm t)

lc-clTel : ∀ Γ → T (lcTel? 1 (clTel 0 (peCtx Γ)))
lc-clTel P.ε       = tt
lc-clTel (Γ P.▸ A) = ∧T (lc-clTel Γ) (lc-clTy A)

honest-pe : ∀ {Γ} → peCtx Γ ⊢ctx → Honest (peCtx Γ)
honest-pe {P.ε}     _              = tt
honest-pe {Γ P.▸ A} (▸-wf w a) = honest-pe w , ty-sc closed laws a , lc-peTy 0 A

------------------------------------------------------------------------
-- ⊤ and ⟦Γ⟧ in ε.

top-wf : ∀ {Θ} → Θ ⊢ctx → Θ ⊢tm topT ∶ ⋆
top-wf w = bnd-wf tt tt w tt (⟨⟩-a w)

ε⧺ : ∀ Δ → (ε ⧺ Δ) ≡ Δ
ε⧺ ε             = refl
ε⧺ (Δ ▸[ ms ] A) = cong (_▸[ ms ] A) (ε⧺ Δ)

free-ε : ∀ {Γ} → Γ P.⊢ctx → ε ⊢tm freeP Γ ∶ ⋆
free-ε {Γ} w =
  bnd-wf (sc-clTel 0 (peCtx Γ)) (lc-clTel Γ)
    (subst _⊢ctx (sym (trans (ε⧺ _) (open-cl-id (peCtx Γ) (honest-pe wG)))) wG)
    (∧T {0 ==ℕ 0} tt (sc-clTel 0 (peCtx Γ))) (⟨⟩-a ε-wf)
  where wG = pe-ctx-wf w

------------------------------------------------------------------------
-- Prefixes of a pure context (by level), as in LimPresup.

dropR : Nat → P.Ctx → P.Ctx
dropR zero    Γ         = Γ
dropR (suc k) P.ε       = P.ε
dropR (suc k) (Γ P.▸ _) = dropR k Γ

pre : P.Ctx → Nat → P.Ctx
pre K i = dropR (P.len K ∸ i) K

private
  fromT : ∀ {X : Set} (m : Maybe X) → T (is-just m) → X
  fromT (just x) _ = x

  sub-suc : ∀ m n → T (n <ℕ suc m) → suc m ∸ n ≡ suc (m ∸ n)
  sub-suc m       zero    _ = refl
  sub-suc (suc m) (suc n) p = sub-suc m n p
  sub-suc zero    (suc zero) ()
  sub-suc zero    (suc (suc n)) ()

  n∸n : ∀ n → n ∸ n ≡ 0
  n∸n zero    = refl
  n∸n (suc n) = n∸n n

  sn∸n : ∀ n → suc n ∸ n ≡ 1
  sn∸n zero    = refl
  sn∸n (suc n) = sn∸n n

  ≢→< : ∀ i n → (i ==ℕ n) ≡ false → T (i <ℕ suc n) → T (i <ℕ n)
  ≢→< zero    zero    () _
  ≢→< zero    (suc n) _ _ = tt
  ≢→< (suc i) (suc n) e p = ≢→< i n e p
  ≢→< (suc i) zero    _ ()

  drop-all : ∀ K → dropR (P.len K) K ≡ P.ε
  drop-all P.ε       = refl
  drop-all (K P.▸ _) = drop-all K

lk-range : ∀ K i {A} → P.lookup K i ≡ just A → T (i <ℕ P.len K)
lk-range P.ε       i ()
lk-range (K P.▸ B) i e with i ==ℕ P.len K in q
... | true  rewrite ==→≡ i (P.len K) q = <-self (P.len K)
... | false = <-suc i (P.len K) (lk-range K i e)

lk-in : ∀ K i → T (i <ℕ P.len K) → Σ P.Ty λ A → P.lookup K i ≡ just A
lk-in P.ε       i ()
lk-in (K P.▸ B) i p with i ==ℕ P.len K in q
... | true  = B , refl
... | false = lk-in K i (≢→< i (P.len K) q p)

lk-wf : ∀ {K} → K P.⊢ctx → ∀ i {A} → P.lookup K i ≡ just A →
        (pre K i P.⊢ty A) × (pre K (suc i) ≡ pre K i P.▸ A)
lk-wf {K P.▸ B} (P.▸-wf w b) i e with i ==ℕ P.len K in q
... | true rewrite ==→≡ i (P.len K) q | sn∸n (P.len K) | n∸n (P.len K) with e
...   | refl = b , refl
lk-wf {K P.▸ B} (P.▸-wf w b) i e | false
  rewrite sub-suc (P.len K) i (<-suc i (P.len K) (lk-range K i e))
        | sub-suc (P.len K ∸ suc i) 0 tt =
  let (a , s) = lk-wf w i e in
  a , trans (cong (λ k → dropR k (K P.▸ B)) (sub-eq (P.len K) i (lk-range K i e))) s
  where
  sub-eq : ∀ m i → T (i <ℕ m) → m ∸ i ≡ suc (m ∸ suc i)
  sub-eq (suc m) zero    _ = sym (sub-suc m 0 tt)
  sub-eq (suc m) (suc i) p = sub-eq m i p

------------------------------------------------------------------------
-- The generators, for a well-formed Γ.

genTy-just : ∀ Γ j {A} → P.lookup Γ j ≡ just A → genTy Γ j ≡ peTy (Σty A) [ genSub Γ j ]ty
genTy-just Γ j e with P.lookup Γ j
genTy-just Γ j refl | just _ = refl

module At (Γ : P.Ctx) (wΓ : Γ P.⊢ctx) where

  -- η_{Γ,j}, given that the substitution below it is well typed.
  module Gen (j : Nat) (A : P.Ty) (l : P.lookup Γ j ≡ just A)
             (chk : T (is-just (P.checkCtx Γ)))
             (s : ε ⊢sub genSub Γ j ∶ peCtx (Σctx (pre Γ j))) where

    a : ε ⊢ty peTy (Σty A) [ genSub Γ j ]ty
    a = ty[] closed laws markRen markSub markVar (pe-ty-wf (Σty-wf (fst (lk-wf wΓ j l)))) s

    a′ : ε ⊢ty genTy Γ j
    a′ = subst (ε ⊢ty_) (sym (genTy-just Γ j l)) a

    sc : T (scTy? 0 (genTy Γ j))
    sc = ty-sc closed laws a′

    lc : T (lcTy? 0 (genTy Γ j))
    lc = subst (λ X → T (lcTy? 0 X)) (sym (genTy-just Γ j l))
           (lc-ty[] 0 (peTy (Σty A)) (genSub Γ j) (lc-peTy 0 (Σty A)) (sub-lc s))

    ok : T (sideG (gen Γ) j ε)
    ok = ∧T {true} tt (∧T chk (∧T (subst (λ m → T (is-just m)) (sym l) tt) (∧T sc lc)))

    η-wf : ε ⊢tm genId Γ j ∶ peTy (Σty A) [ genSub Γ j ]ty
    η-wf = subst (ε ⊢tm genId Γ j ∶_) (trans (opTy-lc 0 ⟨⟩ (genTy Γ j) lc) (genTy-just Γ j l))
             (bnd-wf tt tt ε-wf ok (⟨⟩-a ε-wf))

  gen-sub : T (is-just (P.checkCtx Γ)) → ∀ j → T (j <ℕ suc (P.len Γ)) →
            ε ⊢sub genSub Γ j ∶ peCtx (Σctx (pre Γ j))
  gen-sub chk zero _ =
    subst (λ X → ε ⊢sub genSub Γ zero ∶ peCtx (Σctx X)) (sym (drop-all Γ))
      (,-wf (,-wf (⟨⟩-wf ε-wf) (top-wf ε-wf) tt) (free-ε wΓ) tt)
  gen-sub chk (suc j) q =
    subst (λ X → ε ⊢sub genSub Γ (suc j) ∶ peCtx (Σctx X)) (sym (snd (lk-wf wΓ j l)))
      (,-wf s (Gen.η-wf j A l chk s) tt)
    where
    q′ : T (j <ℕ P.len Γ)
    q′ = q
    s = gen-sub chk j (<-trans j (suc j) (suc (P.len Γ)) (<-self j) q)
    A = fst (lk-in Γ j q′)
    l = snd (lk-in Γ j q′)

------------------------------------------------------------------------
-- Every valid head's type is well formed, in ε and so in any context.

gen-ty-ε : ∀ Γ j → T (sideG (gen Γ) j ε) → ε ⊢ty genTy Γ j
gen-ty-ε Γ j p =
  let q   = snd (T∧ {true} p)
      chk = fst (T∧ {is-just (P.checkCtx Γ)} q)
      ej  = fst (T∧ {is-just (P.lookup Γ j)} (snd (T∧ {is-just (P.checkCtx Γ)} q)))
      (A , l) = just-of (P.lookup Γ j) ej
      wΓ  = fromT (P.checkCtx Γ) chk
  in subst (ε ⊢ty_) (sym (genTy-just Γ j l))
       (At.Gen.a Γ wΓ j A l chk (At.gen-sub Γ wΓ chk j (<-suc j (P.len Γ) (lk-range Γ j l))))
  where
  just-of : ∀ {X : Set} (m : Maybe X) → T (is-just m) → Σ X λ x → m ≡ just x
  just-of (just x) _ = x , refl

wk-ε : ∀ {Θ A} → ε ⊢ty A → Θ ⊢ctx → Θ ⊢ty A
wk-ε {ε}           a _              = a
wk-ε {Θ ▸[ ms ] B} a w@(▸-wf wΘ _) = wk-ty closed laws markRen (wk-ε a wΘ) w

prefix-wf : ∀ Θ Ξ → (Θ ⧺ Ξ) ⊢ctx → Θ ⊢ctx
prefix-wf Θ ε            w            = w
prefix-wf Θ (Ξ ▸[ _ ] _) (▸-wf w _) = prefix-wf Θ Ξ w

gen-presup : PresupLaws
gen-presup = record
  { bargs-sc = λ _ _ _ _ _ _ → tt
  ; res-wf   = λ {Θ} {b} {y} {Δ} → res-wf {Θ} {b} {y} {Δ}
  }
  where
  res-wf : ∀ {Θ b y Δ} → T (scTel? (len Θ) Δ) → T (lcTel? 1 Δ) →
           (Θ ⧺ openTel (len Θ) Δ) ⊢ctx → T (sideG b y Δ) →
           (Θ ⧺ openTel (len Θ) (argsG b y Δ)) ⊢ty opTy 0 (fresh (len Θ) 0) (resG b y Δ)
  res-wf {Θ} {frF free} {y} {Δ} _ _ w _ = ⋆-wf (prefix-wf Θ (openTel (len Θ) Δ) w)
  res-wf {Θ} {unit}     {y} {Δ} _ _ w _ = ⋆-wf (prefix-wf Θ (openTel (len Θ) Δ) w)
  res-wf {Θ} {gen Γ}    {j} {ε} _ _ w p =
    subst (Θ ⊢ty_) (sym (opTy-lc 0 _ (genTy Γ j) (snd (T∧ {scTy? 0 (genTy Γ j)} q₄))))
      (wk-ε (gen-ty-ε Γ j p) w)
    where
    q₁ = snd (T∧ {true} p)
    q₂ = snd (T∧ {is-just (P.checkCtx Γ)} q₁)
    q₄ = snd (T∧ {is-just (P.lookup Γ j)} q₂)
  res-wf {Θ} {gen Γ} {j} {_ ▸[ _ ] _} _ _ _ ()

-- Every term of CaTT with ⟦Γ⟧, ⊤ and η has a well-formed type.
gen-tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
gen-tm-ty = tm-ty closed laws markRen markSub markVar (λ {_} {k} _ _ → ⊥-elim k) gen-presup
