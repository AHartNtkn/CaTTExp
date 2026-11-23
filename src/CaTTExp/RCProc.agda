------------------------------------------------------------------------
-- A relative-coherence procedure whose answers are well typed by proof
-- (ledger S20 (i), notes/rc-generator.md §1).
--
--   rcP : Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Σ w. Γ ⊢tm w ∶ arr A t u)
--
-- No answer is run through the checker. Each case builds its derivation
-- from a proved lemma:
--   * t ≡ u: the identity coherence over the disk Dsk (dim A), as the
--     globular filler on the disk pulled back along dskSub t A;
--   * dimension 1 (A = x → y): the chain filler, GraphFillerTotal.total;
--   * Γ globular: the globular filler, FillTotal.fill-total.
-- Totality is proved for the first two cases: `rcP-id` (every t ≡ u is
-- answered) and `rcP-1` (every 1-dimensional query with equal paths is
-- answered). Totality on globular contexts (needing completeness of
-- glob? and fuel independence of sameNf?) is not yet proved. The remaining cases of rc (Theorem A,
-- the rank >= 3 reductions, the descent) still come from certified
-- tables (CaTTExp.RCOracle) until they are formalized here.
------------------------------------------------------------------------
module CaTTExp.RCProc where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (tm-ty; tm-ctx; ps-wf; Dsk; dsk-ps; dsk-wf; dskSub; sphSub; aL-sph; lenₛ-sph; sc-aL'; lk-top)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.GlobularFiller using (LT; lt; nf; fillRaw; ltEq; ltEqs; depthTm; module Lists)
open Lists using (listEq)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.NfCoh using (res-nf)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn; ps-glob)
open import CaTTExp.GlobularTotal.FillTotal using (fill-total)
import CaTTExp.GraphFillerTotal as GT

Ans : Ctx → Ty → Tm → Tm → Set
Ans Γ A t u = Σ Tm λ w → Γ ⊢tm w ∶ arr A t u

------------------------------------------------------------------------
-- Booleans and decidable equalities.

∧-split : ∀ a b → T (a ∧ b) → T a × T b
∧-split true  b p = tt , p
∧-split false b ()

listEq-sound : ∀ xs ys → T (listEq xs ys) → xs ≡ ys
listEq-sound []       []       _ = refl
listEq-sound (x ∷ xs) (y ∷ ys) p with ∧-split (x ==ℕ y) (listEq xs ys) p
... | px , pxs = cong₂ _∷_ (==ℕ-sound x y px) (listEq-sound xs ys pxs)
listEq-sound []       (_ ∷ _)  ()
listEq-sound (_ ∷ _)  []       ()

mutual
  ltEq-sound : ∀ a b → T (ltEq a b) → a ≡ b
  ltEq-sound (lt os cs) (lt os' cs') p with ∧-split (listEq os os') (ltEqs cs cs') p
  ... | po , pc = cong₂ lt (listEq-sound os os' po) (ltEqs-sound cs cs' pc)

  ltEqs-sound : ∀ cs ds → T (ltEqs cs ds) → cs ≡ ds
  ltEqs-sound []       []       _ = refl
  ltEqs-sound (c ∷ cs) (d ∷ ds) p with ∧-split (ltEq c d) (ltEqs cs ds) p
  ... | pc , pcs = cong₂ _∷_ (ltEq-sound c d pc) (ltEqs-sound cs ds pcs)
  ltEqs-sound []       (_ ∷ _)  ()
  ltEqs-sound (_ ∷ _)  []       ()

-- Decide a Boolean, keeping the proof.
decide : (b : Bool) → Maybe (T b)
decide true  = just tt
decide false = nothing

------------------------------------------------------------------------
-- Same strict normal form (globular contexts).

SameNf : Ctx → Tm → Tm → Set
SameNf Γ u v = Σ LT λ N → Σ Nat λ n → Σ Nat λ n′ → (nf n Γ u ≡ just N) × (nf n′ Γ v ≡ just N)

sameNf? : ∀ Γ u v → Maybe (SameNf Γ u v)
sameNf? Γ u v with nf (suc (depthTm u)) Γ u in eu | nf (suc (depthTm v)) Γ v in ev
... | just a | just b with ltEq a b in q
...   | true  = just (a , suc (depthTm u) , suc (depthTm v) , eu , trans ev (cong just (sym (ltEq-sound a b (subst T (sym q) tt)))))
...   | false = nothing
sameNf? Γ u v | _ | _ = nothing

------------------------------------------------------------------------
-- Case 1: globular contexts.

rc-glob : ∀ {Γ A t u} → Glob Γ → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → SameNf Γ t u → Ans Γ A t u
rc-glob g dt du (N , n , n′ , et , eu) with fill-total g dt du N n n′ et eu
... | c , _ , dc = c , dc

------------------------------------------------------------------------
-- Case 2: identities, by the filler on the disk pulled back.

-- Closing a pasting derivation by descending its last cell.
ps-down : ∀ {Γ} k {x} → Γ ⊢ps x ∶ aL k → Γ ⊢ps
ps-down zero    p = ps p
ps-down (suc k) p = ps-down k (psd p)

rc-id : ∀ {Γ A t} → Γ ⊢tm t ∶ A → Ans Γ A t t
rc-id {Γ} {A} {t} dt = w , subst (Γ ⊢tm w ∶_) tyEq (S.tm[] closed dc (dsk-wf dt))
  where
  m   = dim A
  Δ   = Dsk m
  pΔ  = dsk-ps m
  dx  : Δ ⊢tm var (dbl m) ∶ aL m
  dx  = snd (ps-wf pΔ)
  gΔ  : Glob Δ
  gΔ  = ps-glob (ps-down m pΔ)
  r   = res-nf gΔ dx
  same : SameNf Δ (var (dbl m)) (var (dbl m))
  same = fst r , suc (depthTm (var (dbl m))) , suc (depthTm (var (dbl m))) , fst (snd r) , fst (snd r)
  cd  = rc-glob gΔ dx dx same
  c   = fst cd
  dc  = snd cd
  σ   = dskSub t A
  w   = c [ σ ]tm
  sc  = sc-aL' A
  topσ : var (dbl m) [ σ ]tm ≡ t
  topσ = subst (λ k → lookupₛ (sphSub A ,ₛ t) k ≡ t) (lenₛ-sph A) (lk-top (sphSub A) t)
  tyEq : arr (aL m) (var (dbl m)) (var (dbl m)) [ σ ]ty ≡ arr A t t
  tyEq = cong₂ (λ X y → arr X y y) (trans (S.ext-ty (aL m) (sphSub A) t sc) (aL-sph A)) topσ

------------------------------------------------------------------------
-- Case 3: dimension 1, by the chain filler.

rc-1 : ∀ {Γ a b u v} → Γ ⊢tm u ∶ arr ⋆ (var a) (var b) → Γ ⊢tm v ∶ arr ⋆ (var a) (var b) →
       GT.path u ≡ GT.path v → Ans Γ (arr ⋆ (var a) (var b)) u v
rc-1 du dv pe = _ , GT.total du dv pe

------------------------------------------------------------------------
-- Deciding that a context is globular.

private
  just-inj′ : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj′ refl = refl

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-suc′ : ∀ a → T (a <ℕ suc a)
  <-suc′ zero    = tt
  <-suc′ (suc a) = <-suc′ a

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (subst T (sym eq) tt) = <-suc′ (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

  <-pred : ∀ y k → T (y <ℕ suc k) → (y ==ℕ k) ≡ false → T (y <ℕ k)
  <-pred zero    zero    p ()
  <-pred zero    (suc k) p e = tt
  <-pred (suc y) zero    () e
  <-pred (suc y) (suc k) p e = <-pred y k p e

lookupEq? : ∀ Γ a B → Maybe (lookup Γ a ≡ just B)
lookupEq? Γ a B with lookup Γ a
... | nothing = nothing
... | just C with C ==Ty B in q
...   | true  = just (cong just (==Ty-sound C B (subst T (sym q) tt)))
...   | false = nothing

tyIn? : ∀ Γ A → Maybe (TyIn Γ A)
tyIn? Γ ⋆ = just tt
tyIn? Γ (arr B (var a) (var b)) =
  decide (a <ℕ len Γ) >>= λ pa →
  decide (b <ℕ len Γ) >>= λ pb →
  lookupEq? Γ a B >>= λ ea →
  lookupEq? Γ b B >>= λ eb →
  tyIn? Γ B >>= λ t →
  just (pa , pb , ea , eb , t)
tyIn? Γ _ = nothing

GlobBelow : Ctx → Nat → Set
GlobBelow Γ k = ∀ y A → T (y <ℕ k) → lookup Γ y ≡ just A → TyIn Γ A

entry? : ∀ Γ k → Maybe (∀ A → lookup Γ k ≡ just A → TyIn Γ A)
entry? Γ k with lookup Γ k
... | nothing = just (λ A ())
... | just B  = tyIn? Γ B >>= λ t → just (λ A e → subst (TyIn Γ) (just-inj′ e) t)

globBelow? : ∀ Γ k → Maybe (GlobBelow Γ k)
globBelow? Γ zero    = just (λ y A ())
globBelow? Γ (suc k) =
  globBelow? Γ k >>= λ h →
  entry? Γ k >>= λ hk →
  just (step h hk)
  where
  step : GlobBelow Γ k → (∀ A → lookup Γ k ≡ just A → TyIn Γ A) → GlobBelow Γ (suc k)
  step h hk y A p e with y ==ℕ k in q
  ... | true  = hk A (subst (λ z → lookup Γ z ≡ just A) (==ℕ-sound y k (subst T (sym q) tt)) e)
  ... | false = h y A (<-pred y k p q) e

glob? : ∀ Γ → Maybe (Glob Γ)
glob? Γ = globBelow? Γ (len Γ) >>= λ h → just (λ y A e → h y A (lookup-lt Γ y A e) e)

------------------------------------------------------------------------
-- The procedure.

-- Dimension 1 between variables: the chain filler; otherwise the
-- globular filler when Γ is globular and t, u have one normal form.
via1 : ∀ {Γ} A {t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
via1 (arr ⋆ (var a) (var b)) {t} {u} dt du =
  decide (listEq (GT.path t) (GT.path u)) >>= λ p →
  just (rc-1 dt du (listEq-sound (GT.path t) (GT.path u) p))
via1 _ dt du = nothing

viaGlob : ∀ {Γ A t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
viaGlob {Γ} {A} {t} {u} dt du =
  glob? Γ >>= λ g → sameNf? Γ t u >>= λ s → just (rc-glob g dt du s)

orElse : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
orElse (just x) _ = just x
orElse nothing  m = m

orElse-l : ∀ {X : Set} (m n : Maybe X) → T (is-just m) → T (is-just (orElse m n))
orElse-l (just x) n _ = tt

-- Case split on the Boolean t ==Tm u, kept as an argument so that the
-- totality lemmas below can reason about it.
byEq : ∀ {Γ A t u} (b : Bool) → (T b → t ≡ u) → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
byEq {Γ} {A} {t} true  e dt du = just (subst (Ans Γ A t) (e tt) (rc-id dt))
byEq {Γ} {A}     false e dt du = orElse (via1 A dt du) (viaGlob dt du)

rcP : ∀ {Γ A t u} → Γ ⊢tm t ∶ A → Γ ⊢tm u ∶ A → Maybe (Ans Γ A t u)
rcP {t = t} {u} = byEq (t ==Tm u) (==Tm-sound t u)

------------------------------------------------------------------------
-- Totality on the identity and dimension-1 cases.

∧-intro′ : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro′ {true} _ q = q

mutual
  ==Ty-refl : ∀ A → T (A ==Ty A)
  ==Ty-refl ⋆           = tt
  ==Ty-refl (arr A t u) = ∧-intro′ (==Ty-refl A) (∧-intro′ (==Tm-refl t) (==Tm-refl u))

  ==Tm-refl : ∀ t → T (t ==Tm t)
  ==Tm-refl (var i)     = ==ℕ-refl i
  ==Tm-refl (coh Γ A σ) = ∧-intro′ (==Ctx-refl Γ) (∧-intro′ (==Ty-refl A) (==Sub-refl σ))
  ==Tm-refl (cst ())

  ==Ctx-refl : ∀ Γ → T (Γ ==Ctx Γ)
  ==Ctx-refl ε       = tt
  ==Ctx-refl (Γ ▸ A) = ∧-intro′ (==Ctx-refl Γ) (==Ty-refl A)

  ==Sub-refl : ∀ σ → T (σ ==Sub σ)
  ==Sub-refl ⟨⟩       = tt
  ==Sub-refl (σ ,ₛ t) = ∧-intro′ (==Sub-refl σ) (==Tm-refl t)

listEq-refl : ∀ xs → T (listEq xs xs)
listEq-refl []       = tt
listEq-refl (x ∷ xs) = ∧-intro′ (==ℕ-refl x) (listEq-refl xs)

private
  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

decide-just : ∀ {X : Set} b (f : T b → Maybe X) (p : T b) → T (is-just (f p)) → T (is-just (decide b >>= f))
decide-just true f tt h = h

byEq-true : ∀ {Γ A t u} b e (dt : Γ ⊢tm t ∶ A) (du : Γ ⊢tm u ∶ A) → T b → T (is-just (byEq b e dt du))
byEq-true true e dt du _ = tt

-- rcP answers every query t ≡ u.
rcP-id : ∀ {Γ A t} (dt : Γ ⊢tm t ∶ A) → T (is-just (rcP dt dt))
rcP-id {t = t} dt = byEq-true (t ==Tm t) (==Tm-sound t t) dt dt (==Tm-refl t)

via1-1 : ∀ {Γ a b t u} (dt : Γ ⊢tm t ∶ arr ⋆ (var a) (var b)) (du : Γ ⊢tm u ∶ arr ⋆ (var a) (var b)) →
         GT.path t ≡ GT.path u → T (is-just (via1 (arr ⋆ (var a) (var b)) dt du))
via1-1 {t = t} {u} dt du pe =
  decide-just (listEq (GT.path t) (GT.path u)) _
    (subst (λ p → T (listEq p (GT.path u))) (sym pe) (listEq-refl (GT.path u))) tt

-- rcP answers every 1-dimensional query between variables whose two
-- sides have the same path (the hypothesis of GraphFillerTotal.total).
rcP-1 : ∀ {Γ a b t u} (dt : Γ ⊢tm t ∶ arr ⋆ (var a) (var b)) (du : Γ ⊢tm u ∶ arr ⋆ (var a) (var b)) →
        GT.path t ≡ GT.path u → T (is-just (rcP dt du))
rcP-1 {t = t} {u} dt du pe = go (t ==Tm u) (==Tm-sound t u)
  where
  go : ∀ b e → T (is-just (byEq b e dt du))
  go true  e = tt
  go false e = orElse-l (via1 _ dt du) (viaGlob dt du) (via1-1 dt du pe)
