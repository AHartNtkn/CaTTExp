------------------------------------------------------------------------
-- The top-slot congruence cell (ledger S20 (i) stage 3b).
--
-- Let τ = node (t ∷ ts) be a pasting tree with P = ctxOf τ, n = len P,
-- and c = coh P (arr B s u) id a coherence or operation over P. Raise
-- the leaves flagged by bs (all of dimension k, with dim P ≤ k and some
-- leaf flagged) to get R = ctxOf (raiseT bs τ) with its inclusions
-- incl∓ : R → P. If incl⁻ and incl⁺ agree on the variables of the type
-- A = arr B s u (`Agree`), then
--
--   R ⊢ty arr A^ c⁻ c⁺,   A^ = A[incl⁻],  c∓ = c[incl∓]     (`cong-ty`)
--
-- and coh R (arr A^ c⁻ c⁺) is an operation (`cong-side`): its source
-- uses exactly ∂⁻ R and its target exactly ∂⁺ R. So for every
-- Γ ⊢sub σ^ ∶ R, `cong-cell` types the cell
--
--   coh R (arr A^ c⁻ c⁺) σ^ : c[incl⁻ ∘ σ^] → c[incl⁺ ∘ σ^],
--
-- the congruence of c in its flagged top slots: the slots get the
-- sources and targets of the cells σ^ puts on the new top variables.
--
-- `Agree` holds whenever c is an operation over P (`agree-op`): incl∓
-- differ only at flagged leaves, of dimension k (`PsRaise.diff-incl`),
-- and an operation's type uses only ∂⁻ P ∪ ∂⁺ P, whose cells have
-- dimension < dim P ≤ k (`src-small`, `tgt-small`). `cong-cell-op`
-- states the cell for operations with no Agree hypothesis.
------------------------------------------------------------------------
module CaTTExp.PsRaiseCongr where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.Derived
  using (Mem; _⊆_; ≈-absorb; fv-ty[]; agree-ty; idS; id-ty; id-wf; ps-wf; upTo;
         lenₛ-renS; ∨-l; ∨-r; ∧-in; mem-snoc; mem-one; mem++; mem++l; mem++r; <-irr'; _⊎_; inj₁; inj₂)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.VarSubFv using (lev; VarSub; lk-var)
open import CaTTExp.PsRaise
open import CaTTExp.GrayCtx.Lift using (raiseT)

private
  img-++′ : ∀ σ xs ys → img σ (xs ++ ys) ≡ img σ xs ++ img σ ys
  img-++′ σ []       ys = refl
  img-++′ σ (x ∷ xs) ys = cong (_ ∷_) (img-++′ σ xs ys)

  fvTm-var : ∀ u → u ≡ var (lev u) → fvTm u ≡ lev u ∷ []
  fvTm-var (var j) _ = refl

-- The free variables of id ∘ σ, for a variable substitution σ.
fv-idS∘ : ∀ n σ → VarSub σ → fvSub (idS n ∘ σ) ≡ img σ (upTo n)
fv-idS∘ zero    σ v = refl
fv-idS∘ (suc n) σ v =
  trans (cong₂ _++_ (fv-idS∘ n σ v) (fvTm-var (lookupₛ σ n) (lk-var σ n v)))
        (sym (img-++′ σ (upTo n) (n ∷ [])))

module _ (bs : List Bool) (t : Tree) (ts : List Tree) (B : Ty) (s u : Tm) where
  private
    τ = node (t ∷ ts)
    P = ctxOf τ
    n = len P
    R = ctxOf (raiseT bs τ)
    σm = inclM bs t ts
    σp = inclP bs t ts

  A : Ty
  A = arr B s u

  c⁻ c⁺ : Tm
  c⁻ = coh P A (idS n ∘ σm)
  c⁺ = coh P A (idS n ∘ σp)

  A^ : Ty
  A^ = A [ σm ]ty

  Agree : Set
  Agree = ∀ w → Mem w (fvTy A) → lookupₛ σp w ≡ lookupₛ σm w

  private
    wP : P ⊢ctx
    wP = fst (ps-wf (snd (snd (build τ pss))))

    wR : R ⊢ctx
    wR = fst (ps-wf (snd (snd (build (raiseT bs τ) pss))))

    scA : P ⊢ty A → Sb.ScTy n A
    scA a = Sb.ty-sc closed a

    lenId : lenₛ (idS n) ≡ n
    lenId = lenₛ-renS n (λ i → i)

    scId : ∀ σ → P ⊢ty A → Sb.ScTy (lenₛ (idS n ∘ σ)) A
    scId σ a = subst (λ m → Sb.ScTy m A) (sym (trans (Sb.lenₛ-∘ (idS n) σ) lenId)) (scA a)

    -- A[σ] = A[id ∘ σ], so its variables are among those of id ∘ σ.
    fvA : ∀ σ → P ⊢ty A → fvTy (A [ σ ]ty) ⊆ fvSub (idS n ∘ σ)
    fvA σ a w m =
      fv-ty[] A (idS n ∘ σ) (scId σ a) w
        (subst (λ X → Mem w (fvTy X))
          (trans (cong (_[ σ ]ty) (sym (id-ty n A (scA a))))
                 (Sb.assoc-ty A (idS n) σ (subst (λ m → Sb.ScTy m A) (sym lenId) (scA a)))) m)

    agreeEq : Agree → A [ σp ]ty ≡ A^
    agreeEq g = agree-ty A σp σm g

  cong-ty : P ⊢ty A → T (cattSide P B s u) → Agree → R ⊢ty arr A^ c⁻ c⁺
  cong-ty a side g = arr-wf d⁻ (subst (R ⊢tm c⁺ ∶_) (agreeEq g) d⁺)
    where
    dc : P ⊢tm coh P A (idS n) ∶ A [ idS n ]ty
    dc = coh-wf (snd (psOf τ)) wP a side (id-wf wP)
    d⁻ : R ⊢tm c⁻ ∶ A^
    d⁻ = subst (R ⊢tm c⁻ ∶_) (cong (_[ σm ]ty) (id-ty n A (scA a))) (Sb.tm[] closed dc (inclM-wf bs t ts))
    d⁺ : R ⊢tm c⁺ ∶ A [ σp ]ty
    d⁺ = subst (R ⊢tm c⁺ ∶_) (cong (_[ σp ]ty) (id-ty n A (scA a))) (Sb.tm[] closed dc (inclP-wf bs t ts))

  cong-side : ∀ k → Le (dimCtx P) k → TopOK k 0 (t ∷ ts) bs → T (anyR bs (t ∷ ts)) →
              P ⊢ty A → Agree → T (cattSide R A^ c⁻ c⁺)
  cong-side k le top any a g = ∨-r (∧-in src tgt)
    where
    src : T (≈? (fvTmTy c⁻ A^) (∂⁻ R))
    src = subst (λ L → T (≈? (fvSub (idS n ∘ σm) ++ fvTy A^) L))
            (trans (fv-idS∘ n σm (inclM-var bs t ts)) (sym (src-raise k bs t ts le top any)))
            (≈-absorb (fvSub (idS n ∘ σm)) (fvTy A^) (fvA σm a))
    tgt : T (≈? (fvTmTy c⁺ A^) (∂⁺ R))
    tgt = subst (λ L → T (≈? (fvSub (idS n ∘ σp) ++ fvTy A^) L))
            (trans (fv-idS∘ n σp (inclP-var bs t ts)) (sym (tgt-raise k bs t ts le top any)))
            (≈-absorb (fvSub (idS n ∘ σp)) (fvTy A^)
              (λ w m → fvA σp a w (subst (λ X → Mem w (fvTy X)) (sym (agreeEq g)) m)))

  -- The congruence cell, for any Γ ⊢sub σ^ ∶ R.
  cong-cell : ∀ {Γ σ^} k → Le (dimCtx P) k → TopOK k 0 (t ∷ ts) bs → T (anyR bs (t ∷ ts)) →
              P ⊢ty A → T (cattSide P B s u) → Agree → Γ ⊢sub σ^ ∶ R →
              Γ ⊢tm coh R (arr A^ c⁻ c⁺) σ^ ∶ arr A^ c⁻ c⁺ [ σ^ ]ty
  cong-cell k le top any a side g sσ =
    coh-wf (snd (psOf (raiseT bs τ))) wR (cong-ty a side g) (cong-side k le top any a g) sσ

------------------------------------------------------------------------
-- Discharging Agree for operations.

private
  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} p = p

  ⊆?-sound : ∀ xs ys → T (⊆? xs ys) → xs ⊆ ys
  ⊆?-sound []       ys _ n ()
  ⊆?-sound (x ∷ xs) ys p n m with n ==ℕ x in e
  ... | true  = subst (λ z → Mem z ys) (sym (==ℕ-sound n x (subst T (sym e) tt))) (∧-l p)
  ... | false = ⊆?-sound xs ys (∧-r {elem x ys} p) n m

  just-inj : ∀ {A B : Ty} → just A ≡ just B → A ≡ B
  just-inj refl = refl

  or-map : ∀ a {b c} → T (a ∨ b) → (T b → T c) → T (a ∨ c)
  or-map true  p f = tt
  or-map false p f = f p

  mem-dropLast : ∀ n xs → Mem n (dropLastᴸ xs) → Mem n xs
  mem-dropLast n (x ∷ [])     ()
  mem-dropLast n (x ∷ y ∷ xs) m = or-map (n ==ℕ x) m (mem-dropLast n (y ∷ xs))

  mem-lt : ∀ n xs w → AllLt n xs → Mem w xs → T (w <ℕ n)
  mem-lt n (x ∷ xs) w (p , a) m with w ==ℕ x in e
  ... | true  = subst (λ z → T (z <ℕ n)) (sym (==ℕ-sound w x (subst T (sym e) tt))) p
  ... | false = mem-lt n xs w a m

  neq : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  neq zero    (suc n) _ = refl
  neq (suc i) (suc n) p = neq i n p

  lk-old : ∀ Γ C w → T (w <ℕ len Γ) → lookup (Γ ▸ C) w ≡ lookup Γ w
  lk-old Γ C w p rewrite neq w (len Γ) p = refl

  lk-old2c : ∀ Γ C D w → T (w <ℕ len Γ) → lookup (Γ ▸ C ▸ D) w ≡ lookup Γ w
  lk-old2c Γ C D w p = trans (lk-old (Γ ▸ C) D w (<-suc′ w (len Γ) p)) (lk-old Γ C w p)
    where
    <-suc′ : ∀ i n → T (i <ℕ n) → T (i <ℕ suc n)
    <-suc′ zero    (suc n) _ = tt
    <-suc′ (suc i) (suc n) p = <-suc′ i n p

  -- Order facts.
  le-of-not : ∀ j a → (j <ℕ a) ≡ false → Le a j
  le-of-not j       zero    _ = tt
  le-of-not zero    (suc a) ()
  le-of-not (suc j) (suc a) e = le-of-not j a e

  lt-of-not : ∀ j a → (j <ℕ a) ≡ false → (a ==ℕ j) ≡ false → Le (suc a) j
  lt-of-not zero    zero    _ ()
  lt-of-not (suc j) zero    _ _ = tt
  lt-of-not zero    (suc a) () _
  lt-of-not (suc j) (suc a) e f = lt-of-not j a e f

  le-suc′ : ∀ a j → Le (suc a) j → Le a j
  le-suc′ zero    j       _ = tt
  le-suc′ (suc a) (suc j) p = le-suc′ a j p

  le-eq : ∀ a j → (a ==ℕ j) ≡ true → Le a j
  le-eq zero    zero    _ = tt
  le-eq (suc a) (suc j) e = le-eq a j e

  small-base : ∀ j F → just ⋆ ≡ just F → Le (dim F) j
  small-base j .⋆ refl = tt

-- Cells in ∂⁻ⱼ and ∂⁺ⱼ of a pasting context have dimension ≤ j.
src-small : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ j w F → Mem w (srcVars j Γ) → lookup Γ w ≡ just F → Le (dim F) j
src-small pss j w F m l = small-base j F (subst (λ z → lookup (ε ▸ ⋆) z ≡ just F) (mem-one w 0 m) l)
src-small (psd d) j w F m l = src-small d j w F m l
src-small (pse {Γ} {x} {A} d) j w F m l with j <ℕ suc (dim A) in e
... | true  = src-small d j w F m (trans (sym (lk-old2c Γ A _ w (mem-lt _ _ w (src-lt j Γ) m))) l)
... | false with mem-snoc w (snoc (srcVars j Γ) (len Γ)) (suc (len Γ)) m
...   | inj₂ refl =
  subst (λ X → Le (dim X) j) (just-inj (trans (sym (lookup-top (Γ ▸ A) _)) l)) (le-of-not j (suc (dim A)) e)
...   | inj₁ m′ with mem-snoc w (srcVars j Γ) (len Γ) m′
...     | inj₂ refl =
  subst (λ X → Le (dim X) j) (just-inj (trans (sym (lookup-wk (Γ ▸ A) (len Γ) _ (lookup-top Γ A))) l))
    (le-suc′ (dim A) j (le-of-not j (suc (dim A)) e))
...     | inj₁ m″ = src-small d j w F m″ (trans (sym (lk-old2c Γ A _ w (mem-lt _ _ w (src-lt j Γ) m″))) l)

tgt-small : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ j w F → Mem w (tgtVars j Γ) → lookup Γ w ≡ just F → Le (dim F) j
tgt-small pss j w F m l = small-base j F (subst (λ z → lookup (ε ▸ ⋆) z ≡ just F) (mem-one w 0 m) l)
tgt-small (psd d) j w F m l = tgt-small d j w F m l
tgt-small (pse {Γ} {x} {A} d) j w F m l with j <ℕ dim A in e
... | true  = tgt-small d j w F m (trans (sym (lk-old2c Γ A _ w (mem-lt _ _ w (tgt-lt j Γ) m))) l)
... | false with dim A ==ℕ j in f
...   | true with mem-snoc w (dropLastᴸ (tgtVars j Γ)) (len Γ) m
...     | inj₂ refl =
  subst (λ X → Le (dim X) j) (just-inj (trans (sym (lookup-wk (Γ ▸ A) (len Γ) _ (lookup-top Γ A))) l)) (le-eq (dim A) j f)
...     | inj₁ m′ = tgt-small d j w F (mem-dropLast w (tgtVars j Γ) m′)
                      (trans (sym (lk-old2c Γ A _ w (mem-lt _ _ w (tgt-lt j Γ) (mem-dropLast w (tgtVars j Γ) m′)))) l)
tgt-small (pse {Γ} {x} {A} d) j w F m l | false | false with mem-snoc w (snoc (tgtVars j Γ) (len Γ)) (suc (len Γ)) m
...     | inj₂ refl =
  subst (λ X → Le (dim X) j) (just-inj (trans (sym (lookup-top (Γ ▸ A) _)) l)) (lt-of-not j (dim A) e f)
...     | inj₁ m′ with mem-snoc w (tgtVars j Γ) (len Γ) m′
...       | inj₂ refl =
  subst (λ X → Le (dim X) j) (just-inj (trans (sym (lookup-wk (Γ ▸ A) (len Γ) _ (lookup-top Γ A))) l))
    (le-suc′ (dim A) j (lt-of-not j (dim A) e f))
...       | inj₁ m″ = tgt-small d j w F m″ (trans (sym (lk-old2c Γ A _ w (mem-lt _ _ w (tgt-lt j Γ) m″))) l)

private
  le-tr : ∀ a b c → Le a b → Le b c → Le a c
  le-tr zero    b       c       _ _ = tt
  le-tr (suc a) zero    c       () _
  le-tr (suc a) (suc b) zero    _ ()
  le-tr (suc a) (suc b) (suc c) p q = le-tr a b c p q

  no-top : ∀ a k → Le a k → Le k (a ∸ 1) → T (0 <ℕ k) → ⊥
  no-top zero    (suc k) _ () _
  no-top (suc a) zero    () _ _
  no-top (suc a) (suc k) p q _ = <-irr' k (le-tr (suc k) a k q p)

  wP′ : ∀ t ts → ctxOf (node (t ∷ ts)) ⊢ps fst (snd (build (node (t ∷ ts)) pss)) ∶ ⋆
  wP′ t ts = snd (snd (build (node (t ∷ ts)) pss))

  -- An operation's type uses only ∂⁻ P ∪ ∂⁺ P.
  inBd : ∀ P B s u w → T (isOp P B s u) → Mem w (fvTy (arr B s u)) → Mem w (∂⁻ P) ⊎ Mem w (∂⁺ P)
  inBd P B s u w op m with mem++ w (fvTy B) _ m
  ... | inj₁ b = inj₁ (S⁻ w (mem++r w (fvTm s) _ b))
    where S⁻ = ⊆?-sound (fvTm s ++ fvTy B) (∂⁻ P) (∧-l (∧-l op))
  ... | inj₂ r with mem++ w (fvTm s) _ r
  ...   | inj₁ a = inj₁ (S⁻ w (mem++l w (fvTm s) _ a))
    where S⁻ = ⊆?-sound (fvTm s ++ fvTy B) (∂⁻ P) (∧-l (∧-l op))
  ...   | inj₂ c = inj₂ (S⁺ w (mem++l w (fvTm u) _ c))
    where S⁺ = ⊆?-sound (fvTm u ++ fvTy B) (∂⁺ P) (∧-l (∧-r {≈? (fvTm s ++ fvTy B) (∂⁻ P)} op))

-- For an operation over P, incl⁻ and incl⁺ agree on its type.
agree-op : ∀ bs t ts B s u k → Le (dimCtx (ctxOf (node (t ∷ ts)))) k → TopOK k 0 (t ∷ ts) bs →
           T (isOp (ctxOf (node (t ∷ ts))) B s u) → Agree bs t ts B s u
agree-op bs t ts B s u k le top op w m = go (diff-incl k bs t ts top w lt)
  where
  P = ctxOf (node (t ∷ ts))
  j = dimCtx P ∸ 1
  lt : T (w <ℕ len P)
  lt with inBd P B s u w op m
  ... | inj₁ m′ = mem-lt _ _ w (src-lt j P) m′
  ... | inj₂ m′ = mem-lt _ _ w (tgt-lt j P) m′
  small : ∀ F → lookup P w ≡ just F → Le (dim F) j
  small F l with inBd P B s u w op m
  ... | inj₁ m′ = src-small (wP′ t ts) j w F m′ l
  ... | inj₂ m′ = tgt-small (wP′ t ts) j w F m′ l
  go : (lookupₛ (inclP bs t ts) w ≡ lookupₛ (inclM bs t ts) w) ⊎
       (Σ Ty λ F → (lookup P w ≡ just F) × (dim F ≡ k) × T (0 <ℕ k)) →
       lookupₛ (inclP bs t ts) w ≡ lookupₛ (inclM bs t ts) w
  go (inj₁ e)               = e
  go (inj₂ (F , l , d , z)) = ⊥-elim (no-top (dimCtx P) k le (subst (λ x → Le x j) d (small F l)) z)

-- The congruence cell of an operation, with no further hypothesis.
cong-cell-op : ∀ bs t ts B s u {Γ σ^} k → Le (dimCtx (ctxOf (node (t ∷ ts)))) k → TopOK k 0 (t ∷ ts) bs →
               T (anyR bs (t ∷ ts)) → ctxOf (node (t ∷ ts)) ⊢ty arr B s u →
               T (isOp (ctxOf (node (t ∷ ts))) B s u) → Γ ⊢sub σ^ ∶ ctxOf (raiseT bs (node (t ∷ ts))) →
               Γ ⊢tm coh (ctxOf (raiseT bs (node (t ∷ ts)))) (arr (A^ bs t ts B s u) (c⁻ bs t ts B s u) (c⁺ bs t ts B s u)) σ^
                 ∶ arr (A^ bs t ts B s u) (c⁻ bs t ts B s u) (c⁺ bs t ts B s u) [ σ^ ]ty
cong-cell-op bs t ts B s u k le top any a op sσ =
  cong-cell bs t ts B s u k le top any a (∨-r op) (agree-op bs t ts B s u k le top op) sσ
