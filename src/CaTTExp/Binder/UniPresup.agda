------------------------------------------------------------------------
-- Presupposition for uni (ledger S27 (f′)).
--
-- For every cone shape and every horn shape, every valid head of
-- CaTTExp.Binder.UniHeads has a well-formed type over its arity
-- (`HeadOK`), in the kernel with plain CaTT's side condition and any
-- mark judgment stable under renaming and substitution that gives
-- variables their entry's marks (module parameters; MarkRen, MarkSub,
-- MarkVar). Both rule (MARK) alone (`varMark`) and (MARK) + (HEAD-inv)
-- of CaTTExp.Binder.UniMark qualify. For lim and the legs this is CaTTExp.Binder.LimPresup, reused
-- through its generic part. For uni^y_{Γ,n} (y = 0 the filler w, y ≥ 1
-- the components), with U the horn shape laid out as
--
--   Cone(Γ; L) (p entries) | h horn entries | w | components,
--
-- the substitution ρ of UniHeads (Γ to itself, L to lim_Γ[id], the
-- cone cells to the legs, the horn entries to the arity's variables, w
-- and the earlier components to uni[id]) is shown well typed from the
-- arity into the first i entries of U, for every i ≤ p + h + y:
--
--   * i ≤ p: the cone substitution of LimPresup (`cone-sub`);
--   * p ≤ i ≤ p + h: by induction along the arity, which is built from
--     the horn entries' types under ρ; on the way the arity is shown
--     well formed (`Horn`);
--   * p + h ≤ i ≤ p + h + y: each uni^j[id] (j < y) is valid and typed
--     by rule (op), its type being well formed by the step before.
--
-- The type of entry p + h + y of U under ρ is then well formed over
-- the arity. Validity (`uok`) says only that Γ, the cone shape K and U
-- are well-formed pure contexts, U starts with K, K with Γ, c : ⋆, and
-- the selector is in range; nothing about horns is assumed.
--
-- Hence PresupLaws for CaTT with lim, the universal cone and uni, over
-- any shapes (`uni-presup`, `uni-tm-ty`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.LimHeads
open import CaTTExp.Binder.UniHeads
import CaTTExp.Binder.HeadSpec as HS
import CaTTExp.Binder.LimPresup as LPm
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Typing as Tg
import CaTTExp.Binder.Rename as Rn
import CaTTExp.Binder.Subst as Sb

module CaTTExp.Binder.UniPresup
  (shape : P.Ctx → Maybe P.Ctx) (ushape : P.Ctx → Nat → Maybe UShape)
  (mark : Signature.Ctx (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape)) → BM.Mark →
          Signature.Tm (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape)) → Bool)
  (markRen : Rn.MarkRen (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))
                        (Tg.cattSide (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))) mark)
  (markSub : Sb.MarkSub (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))
                        (Tg.cattSide (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))) mark)
  (markVar : Sb.MarkVar (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))
                        (Tg.cattSide (HS.Laws.𝕊 P.∅ (uniSpec P.K shape ushape))) mark)
  where

open HS.Laws P.∅ (uniSpec P.K shape ushape) using (𝕊; spec-honest; spec-head; spec-laws)
open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Typing 𝕊 using (cattSide)
open import CaTTExp.Binder.TypingWith 𝕊 cattSide mark
open import CaTTExp.Binder.Scoping 𝕊 cattSide mark
open import CaTTExp.Binder.Rename 𝕊 cattSide mark
open import CaTTExp.Binder.Subst 𝕊 cattSide mark
open import CaTTExp.Binder.HonestHeads 𝕊 using (HonestAt; honest?)
open import CaTTExp.Binder.HonestHeads 𝕊 using (module Typed)
open Typed cattSide mark using (op-intro; honest-ok)
import CaTTExp.Binder.Heads 𝕊 as Hd
open Hd.Typed cattSide mark using (HeadOK)
open import CaTTExp.Binder.Presup 𝕊 cattSide mark using (PresupLaws; ty-ctx)
open UniConstruction P.K LUF (λ b → b) shape ushape
open PureEmb P.K LUF
open LC using (shapeOK; dropR)

module LP = LPm shape
module G = LP.Gen (uniSpec P.K shape ushape) base (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  mark markRen markSub markVar
open G using (closed; laws; pe-ty-wf; lc-peTy; len-pe; pre; lk-in; lk-wf; lk-range; idsub)

------------------------------------------------------------------------
-- Arithmetic.

private
  fromT : ∀ {X : Set} (m : Maybe X) → T (is-just m) → X
  fromT (just x) _ = x

  lt-true : ∀ a b → T (a <ℕ b) → (a <ℕ b) ≡ true
  lt-true zero    (suc b) _ = refl
  lt-true (suc a) (suc b) p = lt-true a b p

  -- b ≤ a: a < b is false.
  lt-false : ∀ a b → T (b <ℕ suc a) → (a <ℕ b) ≡ false
  lt-false a       zero    _ = refl
  lt-false zero    (suc b) p = ⊥-elim (lt0 b p)
    where
    lt0 : ∀ b → T (suc b <ℕ 1) → ⊥
    lt0 zero    ()
    lt0 (suc b) ()
  lt-false (suc a) (suc b) p = lt-false a b p

  -- b < a: a = b is false.
  eq-false : ∀ a b → T (b <ℕ a) → (a ==ℕ b) ≡ false
  eq-false (suc a) zero    _ = refl
  eq-false (suc a) (suc b) p = eq-false a b p

  eq-true : ∀ a → (a ==ℕ a) ≡ true
  eq-true zero    = refl
  eq-true (suc a) = eq-true a

  +∸ : ∀ a k → (a + k) ∸ a ≡ k
  +∸ zero    k = refl
  +∸ (suc a) k = +∸ a k

  le-+ : ∀ a k → T (a <ℕ suc (a + k))
  le-+ zero    k = tt
  le-+ (suc a) k = le-+ a k

  lt-+ : ∀ a b k → T (a <ℕ b) → T (a <ℕ b + k)
  lt-+ a b zero    p = subst (λ m → T (a <ℕ m)) (sym (+-zero b)) p
  lt-+ a b (suc k) p = subst (λ m → T (a <ℕ m)) (sym (+-suc b k)) (<-suc a (b + k) (lt-+ a b k p))

  lt-+r : ∀ a k b → T ((a + k) <ℕ b) → T (a <ℕ b)
  lt-+r a k b p = <-trans′ a (a + k) b (le-+ a k) p
    where
    <-trans′ : ∀ i j k → T (i <ℕ suc j) → T (j <ℕ k) → T (i <ℕ k)
    <-trans′ zero    j       (suc k) _ _ = tt
    <-trans′ (suc i) (suc j) (suc k) p q = <-trans′ i j k p q
    <-trans′ (suc i) zero    k       () _

  ∸+ : ∀ a b → T (a <ℕ suc b) → a + (b ∸ a) ≡ b
  ∸+ zero    b       _ = refl
  ∸+ (suc a) (suc b) p = cong suc (∸+ a b p)
  ∸+ (suc a) zero    ()

  lt-add : ∀ a {k h} → T (k <ℕ h) → T ((a + k) <ℕ (a + h))
  lt-add zero    q = q
  lt-add (suc a) q = lt-add a q

  +-assoc : ∀ a b c → a + b + c ≡ a + (b + c)
  +-assoc zero    b c = refl
  +-assoc (suc a) b c = cong suc (+-assoc a b c)

  n∸n : ∀ n → n ∸ n ≡ 0
  n∸n zero    = refl
  n∸n (suc n) = n∸n n

  sub-len : ∀ {Δ σ Θ} → Δ ⊢sub σ ∶ Θ → lenₛ σ ≡ len Θ
  sub-len (⟨⟩-wf _)    = refl
  sub-len (,-wf s _ _) = cong suc (sub-len s)

  len-tab : ∀ k (f : Nat → Tm) → lenₛ (tab k f) ≡ k
  len-tab zero    f = refl
  len-tab (suc k) f = cong suc (len-tab k f)

-- Substituting tab M f into a type scoped below m ≤ M is substituting
-- tab m f.
trunc : ∀ (f : Nat → Tm) m k A → T (scTy? m A) → A [ tab (m + k) f ]ty ≡ A [ tab m f ]ty
trunc f m zero    A s rewrite +-zero m = refl
trunc f m (suc k) A s rewrite +-suc m k =
  trans (ext-ty A (tab (m + k) f) (f (m + k))
           (subst (λ n → T (scTy? n A)) (sym (len-tab (m + k) f)) (scTy-+ m k A s)))
        (trunc f m k A s)

------------------------------------------------------------------------
-- At a valid uni head.

module AtU (Γ : P.Ctx) (n : Nat) (Kc U : P.Ctx) (h : Nat) (ms : List Nat)
           (eK : shape Γ ≡ just Kc) (eU : ushape Γ n ≡ just (ush U h ms))
           (c1 : T (shapeOK Γ Kc)) (c2 : T (is-just (P.checkCtx U)))
           (c3 : T (P.len Kc <ℕ suc (P.len U)))
           (c4 : T (dropR (P.len U ∸ P.len Kc) U P.==Ctx Kc))
           (hon : T (honest? (hornCtx Γ n U h ms (P.len Kc) h))) where

  p  = P.len Kc
  open At Γ n p h

  Gc : Ctx
  Gc = peCtx Γ

  A : Nat → Ctx
  A k = hornCtx Γ n U h ms p k

  Au : Ctx
  Au = A h

  getD : getData Γ n ≡ just (dat Kc U h ms)
  getD rewrite eK | eU = refl

  uctx≡ : uctx Γ n ≡ Au
  uctx≡ rewrite getD = refl

  private
    p₁ = T∧ {is-just (P.checkCtx Γ)} c1
    p₂ = T∧ {is-just (P.checkCtx Kc)} (snd p₁)
    p₃ = T∧ {suc (P.len Γ) <ℕ suc (P.len Kc)} (snd p₂)

  nΓ<p : T (nΓ <ℕ p)
  nΓ<p = fst p₃

  -- Honesty of Γ, a prefix of the arity.
  hon-pre : ∀ k → T (honest? (A k)) → T (honest? Gc)
  hon-pre zero    q = q
  hon-pre (suc k) q = hon-pre k (fst (T∧ {honest? (A k)} q))

  honΓ : T (honest? Gc)
  honΓ = hon-pre h hon

  module AS = G.AtShape Γ Kc eK c1 honΓ

  preU : pre U p ≡ Kc
  preU = P.==Ctx-sound _ _ c4

  -- ρ on Γ, the apex and the cone cells.
  ρ-Γ : ∀ i → T (i <ℕ nΓ) → ρi i ≡ var i
  ρ-Γ i q rewrite lt-true i nΓ q = refl

  ρ-L : ρi nΓ ≡ LC.limId Γ
  ρ-L rewrite lt-false nΓ nΓ (<-self nΓ) | eq-true nΓ = refl

  ρ-leg : ∀ g → T (suc (nΓ + g) <ℕ p) → ρi (suc (nΓ + g)) ≡ LC.legId Γ g
  ρ-leg g q
    rewrite lt-false (suc (nΓ + g)) nΓ (<-suc nΓ (suc (nΓ + g)) (le-+ nΓ g))
          | eq-false (suc (nΓ + g)) nΓ (le-+ nΓ g)
          | lt-true (suc (nΓ + g)) p q
          | +∸ nΓ g = refl

  tab-Γ : ∀ m → T (m <ℕ suc nΓ) → tab m ρi ≡ fresh 0 m
  tab-Γ zero    _ = refl
  tab-Γ (suc m) q = cong₂ _,ₛ_ (tab-Γ m (<-suc m nΓ q)) (ρ-Γ m q)

  tab-cone : ∀ g → T (suc (nΓ + g) <ℕ suc p) → tab (suc (nΓ + g)) ρi ≡ LC.coneSub Γ g
  tab-cone zero q rewrite +-zero nΓ = cong₂ _,ₛ_ (tab-Γ nΓ (<-self nΓ)) ρ-L
  tab-cone (suc g) q rewrite +-suc nΓ g =
    cong₂ _,ₛ_ (tab-cone g (<-suc (suc (nΓ + g)) p q′)) (ρ-leg g q′)
    where
    q′ : T (suc (nΓ + g) <ℕ p)
    q′ = q

  -- ρ on the horn entries, w and the components.
  ρ-horn : ∀ k → T (k <ℕ h) → ρi (p + k) ≡ var (nΓ + k)
  ρ-horn k q
    rewrite lt-false (p + k) nΓ (<-suc nΓ (p + k) (lt-+ nΓ p k nΓ<p))
          | eq-false (p + k) nΓ (lt-+ nΓ p k nΓ<p)
          | lt-false (p + k) p (le-+ p k)
          | lt-true (p + k) (p + h) (lt-add p q)
          | +∸ p k = refl

  ρ-uni : ∀ j → ρi (p + h + j) ≡ uniId j
  ρ-uni j
    rewrite lt-false (p + h + j) nΓ (<-suc nΓ (p + h + j) (lt-+ nΓ (p + h) j (lt-+ nΓ p h nΓ<p)))
          | eq-false (p + h + j) nΓ (lt-+ nΓ (p + h) j (lt-+ nΓ p h nΓ<p))
          | lt-false (p + h + j) p (subst (λ m → T (p <ℕ suc m)) (sym (+-assoc p h j)) (le-+ p (h + j)))
          | lt-false (p + h + j) (p + h) (le-+ (p + h) j)
          | +∸ (p + h) j = refl

  wU : U P.⊢ctx
  wU = fromT (P.checkCtx U) c2

  -- The cone part: ρ is the cone substitution of LimPresup.
  g₀ : Nat
  g₀ = p ∸ suc nΓ

  g₀-eq : suc (nΓ + g₀) ≡ p
  g₀-eq = ∸+ (suc nΓ) p nΓ<p

  preKc : pre Kc p ≡ Kc
  preKc = cong (λ k → dropR k Kc) (n∸n p)

  S₀ : Gc ⊢sub tab p ρi ∶ peCtx (pre U p)
  S₀ = subst (λ X → Gc ⊢sub tab p ρi ∶ peCtx X) (trans preKc (sym preU)) step₂
    where
    step₁ : Gc ⊢sub tab (suc (nΓ + g₀)) ρi ∶ peCtx (pre Kc (suc (nΓ + g₀)))
    step₁ = subst (λ σ → Gc ⊢sub σ ∶ peCtx (pre Kc (suc (nΓ + g₀))))
              (sym (tab-cone g₀ (subst (λ m → T (m <ℕ suc p)) (sym g₀-eq) (<-self p))))
              (AS.cone-sub g₀ (subst (λ m → T ((nΓ + g₀) <ℕ m)) g₀-eq (<-self (nΓ + g₀))))
    step₂ : Gc ⊢sub tab p ρi ∶ peCtx (pre Kc p)
    step₂ = subst (λ m → Gc ⊢sub tab m ρi ∶ peCtx (pre Kc m)) g₀-eq step₁

  -- The type of an entry under ρ (the arity's entries and the heads'
  -- types use all of ρ) is its type under the first i entries.
  X≡ : ∀ i B → T (i <ℕ suc (P.len U)) → T (scTy? i (peTy B)) →
       peTy B [ ρ (P.len U) ]ty ≡ peTy B [ tab i ρi ]ty
  X≡ i B q sc =
    trans (cong (λ m → peTy B [ tab m ρi ]ty) (sym (∸+ i (P.len U) q)))
          (trunc ρi i (P.len U ∸ i) (peTy B) sc)

  -- Entry i of U, well formed over the first i entries.
  module Entry (i : Nat) (q : T (i <ℕ P.len U)) where
    Bᵢ : P.Ty
    Bᵢ = fst (lk-in U i q)
    l : P.lookup U i ≡ just Bᵢ
    l = snd (lk-in U i q)
    bwf : pre U i P.⊢ty Bᵢ
    bwf = fst (lk-wf wU i l)
    pre-suc : pre U (suc i) ≡ pre U i P.▸ Bᵢ
    pre-suc = snd (lk-wf wU i l)
    pwf : peCtx (pre U i) ⊢ty peTy Bᵢ
    pwf = pe-ty-wf bwf
    -- Under a well-typed ρ-prefix.
    module Under {Ξ} (s : Ξ ⊢sub tab i ρi ∶ peCtx (pre U i)) where
      a : Ξ ⊢ty peTy Bᵢ [ tab i ρi ]ty
      a = ty[] closed laws markRen markSub markVar pwf s
      sc : T (scTy? i (peTy Bᵢ))
      sc = subst (λ m → T (scTy? m (peTy Bᵢ))) (trans (sym (sub-len s)) (len-tab i ρi)) (ty-sc closed laws pwf)
      eq : peTy Bᵢ [ ρ (P.len U) ]ty ≡ peTy Bᵢ [ tab i ρi ]ty
      eq = X≡ i Bᵢ (<-suc i (P.len U) q) sc
      a′ : Ξ ⊢ty peTy Bᵢ [ ρ (P.len U) ]ty
      a′ = subst (Ξ ⊢ty_) (sym eq) a
      lc : T (lcTy? 0 (peTy Bᵢ [ ρ (P.len U) ]ty))
      lc = subst (λ X → T (lcTy? 0 X)) (sym eq) (lc-ty[] 0 (peTy Bᵢ) (tab i ρi) (lc-peTy Bᵢ) (sub-lc s))
      -- Extending ρ by a term of the right type.
      ext : ∀ {t} → Ξ ⊢tm t ∶ peTy Bᵢ [ tab i ρi ]ty → ρi i ≡ t →
            Ξ ⊢sub tab (suc i) ρi ∶ peCtx (pre U (suc i))
      ext {t} d e = subst (λ X → Ξ ⊢sub tab (suc i) ρi ∶ peCtx X) (sym pre-suc)
                      (subst (λ u → Ξ ⊢sub tab i ρi ,ₛ u ∶ peCtx (pre U i) ▸ peTy Bᵢ) (sym e) (,-wf s d tt))

  -- The arity, entry by entry.
  mk : Nat → List Mark
  mk k = if elem (p + k) ms then minv ∷ [] else []

  A-suc : ∀ k Bᵢ → P.lookup U (p + k) ≡ just Bᵢ → A (suc k) ≡ (A k ▸[ mk k ] (peTy Bᵢ [ ρ (P.len U) ]ty))
  A-suc k Bᵢ e rewrite e = refl

  record W (k : Nat) : Set where
    field
      wA : A k ⊢ctx
      lA : len (A k) ≡ nΓ + k
      sA : A k ⊢sub tab (p + k) ρi ∶ peCtx (pre U (p + k))

  hU : T ((p + h) <ℕ suc (P.len U)) → ∀ k → T (k <ℕ suc h) → W k
  hU _ zero _ = record
    { wA = AS.wG
    ; lA = trans (len-pe Γ) (sym (+-zero nΓ))
    ; sA = subst (λ m → Gc ⊢sub tab m ρi ∶ peCtx (pre U m)) (sym (+-zero p)) S₀ }
  hU b (suc k) r = record { wA = wA′ ; lA = lA′ ; sA = sA′ }
    where
    open W (hU b k (<-suc k h r))
    i = p + k
    q : T (i <ℕ P.len U)
    q = lt-+r (p + k) 0 (P.len U) (subst (λ m → T (m <ℕ P.len U)) (sym (+-zero (p + k)))
          (<-trans′′ (p + k) (p + h) (P.len U) (lt-add p r) b))
      where
      <-trans′′ : ∀ i j k → T (i <ℕ j) → T (j <ℕ suc k) → T (i <ℕ k)
      <-trans′′ zero    (suc j) (suc k) _ _ = tt
      <-trans′′ (suc i) (suc j) (suc k) p q = <-trans′′ i j k p q
      <-trans′′ zero    (suc j) zero    _ ()
      <-trans′′ (suc i) (suc j) zero    _ ()
    open Entry i q
    open Under sA
    X = peTy Bᵢ [ ρ (P.len U) ]ty
    E = A k ▸[ mk k ] X
    wE : E ⊢ctx
    wE = ▸-wf wA a′
    eA : A (suc k) ≡ E
    eA = A-suc k Bᵢ l
    wA′ : A (suc k) ⊢ctx
    wA′ = subst _⊢ctx (sym eA) wE
    lA′ : len (A (suc k)) ≡ nΓ + suc k
    lA′ = trans (cong len eA) (trans (cong suc lA) (sym (+-suc nΓ k)))
    vE : E ⊢tm var (nΓ + k) ∶ peTy Bᵢ [ tab i ρi ]ty
    vE = subst (E ⊢tm var (nΓ + k) ∶_) eq
           (var-wf wE (lookup-top (A k) {mk k} X (nΓ + k) (==-self (sym lA))))
    sE : E ⊢sub tab (suc i) ρi ∶ peCtx (pre U (suc i))
    sE = Under.ext {E} (wk-sub closed laws markRen (ty-ctx pwf) sA wE) vE (ρ-horn k r)
    sA′ : A (suc k) ⊢sub tab (p + suc k) ρi ∶ peCtx (pre U (p + suc k))
    sA′ = subst (λ Ξ → Ξ ⊢sub tab (p + suc k) ρi ∶ peCtx (pre U (p + suc k))) (sym eA)
            (subst (λ m → E ⊢sub tab m ρi ∶ peCtx (pre U m)) (sym (+-suc p k)) sE)

  -- uni at selector j, read off the shapes.
  uok≡ : ∀ j → uok Γ n j ≡ (shapeOK Γ Kc ∧ is-just (P.checkCtx U) ∧ (p <ℕ suc (P.len U)) ∧
                            (dropR (P.len U ∸ p) U P.==Ctx Kc) ∧ ((p + h + j) <ℕ P.len U))
  uok≡ j rewrite getD = refl

  uty≡ : ∀ j Bj → P.lookup U (p + h + j) ≡ just Bj → uty Γ n j ≡ peTy Bj [ ρ (P.len U) ]ty
  uty≡ j Bj e rewrite getD | e = refl

  module Comps (y : Nat) (c5 : T ((p + h + y) <ℕ P.len U)) where
    b : T ((p + h) <ℕ suc (P.len U))
    b = <-suc (p + h) (P.len U) (lt-+r (p + h) y (P.len U) c5)

    WA = hU b h (<-self h)
    open W WA renaming (wA to wAu; lA to lAu; sA to sAu)

    idAu : Au ⊢sub fresh 0 (nΓ + h) ∶ uctx Γ n
    idAu = subst (λ X → Au ⊢sub fresh 0 (nΓ + h) ∶ X) (sym uctx≡)
             (subst (λ m → Au ⊢sub fresh 0 m ∶ Au) lAu (idsub wAu))

    Sc : ∀ j → T (j <ℕ suc y) → Au ⊢sub tab (p + h + j) ρi ∶ peCtx (pre U (p + h + j))
    Sc zero _ = subst (λ m → Au ⊢sub tab m ρi ∶ peCtx (pre U m)) (sym (+-zero (p + h))) sAu
    Sc (suc j) r =
      subst (λ m → Au ⊢sub tab m ρi ∶ peCtx (pre U m)) (sym (+-suc (p + h) j))
        (ext d′ (ρ-uni j))
      where
      i = p + h + j
      qj : T (i <ℕ P.len U)
      qj = <-trans i (p + h + y) (P.len U) (lt-add (p + h) r) c5
      open Entry i qj
      open Under (Sc j (<-suc j y r))
      aj : Au ⊢ty uty Γ n j
      aj = subst (Au ⊢ty_) (sym (uty≡ j Bᵢ l)) a′
      okj : T (bside (uniF Γ n) j ε)
      okj = ∧T {uok Γ n j}
              (subst T (sym (uok≡ j)) (∧T c1 (∧T c2 (∧T c3 (∧T c4 qj)))))
              (∧T {honest? (uctx Γ n)} (subst (λ X → T (honest? X)) (sym uctx≡) hon)
                 (∧T {scTy? (len (uctx Γ n)) (uty Γ n j)}
                    (subst (λ X → T (scTy? (len X) (uty Γ n j))) (sym uctx≡) (ty-sc closed laws aj))
                    (subst (λ X → T (lcTy? 0 X)) (sym (uty≡ j Bᵢ l)) lc)))
      dj : Au ⊢tm uniId j ∶ uty Γ n j [ fresh 0 (nΓ + h) ]ty
      dj = op-intro (spec-honest (uniF Γ n) j okj) okj wAu idAu
      scN : T (scTy? (nΓ + h) (uty Γ n j))
      scN = subst (λ m → T (scTy? m (uty Γ n j))) lAu (ty-sc closed laws aj)
      d′ : Au ⊢tm uniId j ∶ peTy Bᵢ [ tab i ρi ]ty
      d′ = subst (Au ⊢tm uniId j ∶_)
             (trans (id-ty (nΓ + h) (uty Γ n j) scN) (trans (uty≡ j Bᵢ l) eq)) dj

    -- The type of uni^y is well formed over its arity.
    ty-ok : uctx Γ n ⊢ty uty Γ n y
    ty-ok = subst (_⊢ty uty Γ n y) (sym uctx≡)
              (subst (Au ⊢ty_) (sym (uty≡ y Bᵢ l)) a′)
      where
      open Entry (p + h + y) c5
      open Under (Sc y (<-self y))

------------------------------------------------------------------------
-- HeadOK for every head, and presupposition.

private
  conj : P.Ctx → P.Ctx → P.Ctx → Nat → Nat → Bool
  conj Γ Kc U h y = shapeOK Γ Kc ∧ is-just (P.checkCtx U) ∧ (P.len Kc <ℕ suc (P.len U)) ∧
                    (dropR (P.len U ∸ P.len Kc) U P.==Ctx Kc) ∧ ((P.len Kc + h + y) <ℕ P.len U)

  record Inv (Γ : P.Ctx) (n y : Nat) : Set where
    field
      Kc U : P.Ctx
      h    : Nat
      ms   : List Nat
      eK   : shape Γ ≡ just Kc
      eU   : ushape Γ n ≡ just (ush U h ms)

  inv : ∀ Γ n y → T (uok Γ n y) → Inv Γ n y
  inv Γ n y p with shape Γ in eK | ushape Γ n in eU
  ... | just Kc | just (ush U h ms) = record { Kc = Kc ; U = U ; h = h ; ms = ms ; eK = eK ; eU = eU }
  ... | just _  | nothing = ⊥-elim p
  ... | nothing | _       = ⊥-elim p

  uok-eq : ∀ Γ n y {Kc U h ms} → shape Γ ≡ just Kc → ushape Γ n ≡ just (ush U h ms) →
           uok Γ n y ≡ conj Γ Kc U h y
  uok-eq Γ n y eK eU rewrite eK | eU = refl

  uctx-eq : ∀ Γ n {Kc U h ms} → shape Γ ≡ just Kc → ushape Γ n ≡ just (ush U h ms) →
            uctx Γ n ≡ hornCtx Γ n U h ms (P.len Kc) h
  uctx-eq Γ n eK eU rewrite eK | eU = refl

ok-uni : ∀ Γ n → HeadOK (uniF Γ n)
ok-uni Γ n y (_ ▸[ _ ] _) ()
ok-uni Γ n y ε pr = honest-ok (spec-honest (uniF Γ n) y pr) (Comps.ty-ok y c5) ε pr
  where
  q₀ = T∧ {uok Γ n y} pr
  I = inv Γ n y (fst q₀)
  open Inv I
  cj : T (conj Γ Kc U h y)
  cj = subst T (uok-eq Γ n y eK eU) (fst q₀)
  o₁ = T∧ {shapeOK Γ Kc} cj
  o₂ = T∧ {is-just (P.checkCtx U)} (snd o₁)
  o₃ = T∧ {P.len Kc <ℕ suc (P.len U)} (snd o₂)
  o₄ = T∧ {dropR (P.len U ∸ P.len Kc) U P.==Ctx Kc} (snd o₃)
  hon : T (honest? (hornCtx Γ n U h ms (P.len Kc) h))
  hon = subst (λ X → T (honest? X)) (uctx-eq Γ n eK eU) (fst (T∧ {honest? (uctx Γ n)} (snd q₀)))
  c5 = snd o₄
  open AtU Γ n Kc U h ms eK eU (fst o₁) (fst o₂) (fst o₃) (fst o₄) hon

ok-all : ∀ b → HeadOK b
ok-all (base l)   = G.ok-lim l
ok-all (uniF Γ n) = ok-uni Γ n

uni-presup : PresupLaws
uni-presup = G.presup-from ok-all

-- Every term of CaTT with lim, the universal cone and uni, over any
-- shapes, has a well-formed type.
uni-tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
uni-tm-ty = G.tm-ty-from uni-presup
