------------------------------------------------------------------------
-- The range lemma for pasting contexts (open-issues F2a, higher cells).
--
-- Give each object of a pasting context Θ a list T c (later: the path,
-- in a graph context, from the image of the first object to the image
-- of c), monotone along the 1-dimensional variables of Θ in the prefix
-- order. Every variable m has a leftmost object o₀ m and a rightmost
-- object o₁ m (its iterated 0-source and 0-target).
--
-- `range`: every free variable of a well-typed cell t : A of Θ lies
-- between the 0-source and the 0-target of A:
--
--     T (o₀ A) ⊑ T (o₀ m)   and   T (o₁ m) ⊑ T (o₁ A).
--
-- `bdry`: the type of a valid coherence over Θ spans all of Θ: every
-- object c of Θ has T (o₀ A) ⊑ T c ⊑ T (o₁ A). (In the free graph
-- model this says a coherence's boundary is its whole pasting scheme.)
--
-- Both are proved together by structural recursion on terms: the range
-- of a coh over Θ' inside Θ comes from the boundary lemma for Θ', with
-- T pulled back along the coh's argument substitution.
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotal.Range where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal.Chains
open import CaTTExp.GraphFillerTotal using (⋆-var; lookup-wf; tm-ctx)
open import CaTTExp.PureMetatheory using (closed; ty[])
import CaTTExp.Subst ∅ cattSide as S

------------------------------------------------------------------------
-- The prefix order on lists.

infix 4 _⊑_
_⊑_ : List Nat → List Nat → Set
p ⊑ q = Σ (List Nat) λ r → q ≡ p ++ r

++-[] : ∀ (p : List Nat) → p ++ [] ≡ p
++-[] []      = refl
++-[] (x ∷ p) = cong (x ∷_) (++-[] p)

++-assoc : ∀ (p q r : List Nat) → (p ++ q) ++ r ≡ p ++ (q ++ r)
++-assoc []      q r = refl
++-assoc (x ∷ p) q r = cong (x ∷_) (++-assoc p q r)

⊑-refl : ∀ {p} → p ⊑ p
⊑-refl {p} = [] , sym (++-[] p)

⊑-trans : ∀ {p q r} → p ⊑ q → q ⊑ r → p ⊑ r
⊑-trans {p} (a , refl) (b , refl) = a ++ b , ++-assoc p a b

⊑-[] : ∀ p → [] ⊑ p
⊑-[] p = p , refl

⊑-++ : ∀ p q → p ⊑ p ++ q
⊑-++ p q = q , refl

------------------------------------------------------------------------
-- Leftmost and rightmost objects.

vi : Tm → Nat
vi (var i) = i
vi _       = 0

o₀Ty o₁Ty : Ty → Nat
o₀Ty ⋆                     = 0
o₀Ty (arr ⋆ s _)           = vi s
o₀Ty (arr (arr B s t) _ _) = o₀Ty (arr B s t)
o₁Ty ⋆                     = 0
o₁Ty (arr ⋆ _ t)           = vi t
o₁Ty (arr (arr B s t) _ _) = o₁Ty (arr B s t)

o₀M o₁M : Nat → Maybe Ty → Nat
o₀M m (just (arr B s t)) = o₀Ty (arr B s t)
o₀M m _                  = m
o₁M m (just (arr B s t)) = o₁Ty (arr B s t)
o₁M m _                  = m

o₀V o₁V : Ctx → Nat → Nat
o₀V Θ m = o₀M m (lookup Θ m)
o₁V Θ m = o₁M m (lookup Θ m)

-- Not the type of objects.
NS : Ty → Set
NS ⋆           = ⊥
NS (arr _ _ _) = ⊤

------------------------------------------------------------------------
-- Lookup.

lookup-< : ∀ {Γ i A} → lookup Γ i ≡ just A → i < len Γ
lookup-< {Γ ▸ B} {i} eq with i ==ℕ len Γ in e
... | true  = subst (_< suc (len Γ)) (sym (==ℕ-sound i (len Γ) (subst T (sym e) tt))) ≤-refl
... | false = ≤-step (lookup-< {Γ} eq)

lookup-cases : ∀ Γ A i {B} → lookup (Γ ▸ A) i ≡ just B →
               ((i ≡ len Γ) × (A ≡ B)) ⊎ ((i < len Γ) × (lookup Γ i ≡ just B))
lookup-cases Γ A i eq with i ==ℕ len Γ in e
... | true  = inj₁ (==ℕ-sound i (len Γ) (subst T (sym e) tt) , just-inj eq)
  where
  just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
  just-inj refl = refl
... | false = inj₂ (lookup-< {Γ} eq , eq)

lookup-wk : ∀ {Γ A i B} → lookup Γ i ≡ just B → lookup (Γ ▸ A) i ≡ just B
lookup-wk {Γ} {A} {i} eq = trans (lookup-there Γ A i (lookup-< {Γ} eq)) eq

------------------------------------------------------------------------
-- Pasting contexts: the types of variables have variable end points.

VarIs : Ctx → Ty → Tm → Set
VarIs Θ B (var c) = lookup Θ c ≡ just B
VarIs Θ B _       = ⊥

GoodTy : Ctx → Ty → Set
GoodTy Θ ⋆           = ⊤
GoodTy Θ (arr B s t) = VarIs Θ B s × VarIs Θ B t

Good : Ctx → Set
Good Θ = ∀ j B → lookup Θ j ≡ just B → GoodTy Θ B

private
  varIs-wk : ∀ {Γ A B} s → VarIs Γ B s → VarIs (Γ ▸ A) B s
  varIs-wk {Γ} (var c) h = lookup-wk {Γ} h

  goodTy-wk : ∀ {Γ A} B → GoodTy Γ B → GoodTy (Γ ▸ A) B
  goodTy-wk ⋆           _       = tt
  goodTy-wk (arr B s t) (a , b) = varIs-wk s a , varIs-wk t b

good : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Good Γ × (lookup Γ x ≡ just A)
good pss = g , refl
  where
  g : Good (ε ▸ ⋆)
  g j B eq with lookup-cases ε ⋆ j eq
  ... | inj₁ (_ , refl) = tt
  ... | inj₂ (() , _)
good (pse {Γ} {x} {A} d) = g , lookup-here (Γ ▸ A) C (suc (len Γ)) refl
  where
  C = arr A (var x) (var (len Γ))
  gd = good d
  lx = snd gd
  g : Good (Γ ▸ A ▸ C)
  g j B eq with lookup-cases (Γ ▸ A) C j eq
  ... | inj₁ (_ , refl) =
        lookup-wk {Γ ▸ A} (lookup-wk {Γ} lx) ,
        lookup-wk {Γ ▸ A} (lookup-here Γ A (len Γ) refl)
  ... | inj₂ (_ , eq') with lookup-cases Γ A j eq'
  ...   | inj₁ (_ , refl) = goodTy-wk B (goodTy-wk B (fst gd x B lx))
  ...   | inj₂ (_ , eq'') = goodTy-wk B (goodTy-wk B (fst gd j B eq''))
good (psd d) with good d
... | g , lf = g , snd (g _ _ lf)

-- The first variable of a pasting context is an object.
ps-0 : ∀ {Γ x A} → Γ ⊢ps x ∶ A → lookup Γ 0 ≡ just ⋆
ps-0 pss = refl
ps-0 (pse {Γ} {x} {A} d) = lookup-wk {Γ ▸ A} {arr A (var x) (var (len Γ))} (lookup-wk {Γ} {A} (ps-0 d))
ps-0 (psd d) = ps-0 d

-- The last pair of a pasting context.
ps-inv : ∀ {Γ A B z C} → (Γ ▸ A ▸ B) ⊢ps z ∶ C →
         Σ Nat λ x → (Γ ⊢ps x ∶ A) × (B ≡ arr A (var x) (var (len Γ)))
ps-inv (pse d) = _ , d , refl
ps-inv (psd d) = ps-inv d

------------------------------------------------------------------------
-- Typing facts.

tm-ty : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ty A
tm-ty (var-wf w eq)        = lookup-wf w eq
tm-ty (coh-wf _ _ a _ s)   = ty[] a s
tm-ty (cst-wf {()} _ _)

-- The end objects of a type, after substitution.
o₀-sub : ∀ {Θ} B ρ → Θ ⊢ty B → NS B → o₀Ty (B [ ρ ]ty) ≡ vi (lookupₛ ρ (o₀Ty B))
o₀-sub (arr ⋆ s t) ρ (arr-wf ds _) _ with ⋆-var ds refl
... | j , refl = refl
o₀-sub (arr (arr B s' t') s t) ρ (arr-wf ds _) _ = o₀-sub (arr B s' t') ρ (tm-ty ds) tt

o₁-sub : ∀ {Θ} B ρ → Θ ⊢ty B → NS B → o₁Ty (B [ ρ ]ty) ≡ vi (lookupₛ ρ (o₁Ty B))
o₁-sub (arr ⋆ s t) ρ (arr-wf _ dt) _ with ⋆-var dt refl
... | j , refl = refl
o₁-sub (arr (arr B s' t') s t) ρ (arr-wf ds _) _ = o₁-sub (arr B s' t') ρ (tm-ty ds) tt

o₀-obj : ∀ {Θ} B → Θ ⊢ty B → NS B → lookup Θ (o₀Ty B) ≡ just ⋆
o₀-obj (arr ⋆ s t) (arr-wf ds _) _ with ⋆-var ds refl
... | j , refl with ds
...   | var-wf _ eq = eq
o₀-obj (arr (arr B s' t') s t) (arr-wf ds _) _ = o₀-obj (arr B s' t') (tm-ty ds) tt

o₁-obj : ∀ {Θ} B → Θ ⊢ty B → NS B → lookup Θ (o₁Ty B) ≡ just ⋆
o₁-obj (arr ⋆ s t) (arr-wf _ dt) _ with ⋆-var dt refl
... | j , refl with dt
...   | var-wf _ eq = eq
o₁-obj (arr (arr B s' t') s t) (arr-wf ds _) _ = o₁-obj (arr B s' t') (tm-ty ds) tt

-- The leftmost object of a type occurs in it.
o₀-fv : ∀ {Θ} B → Θ ⊢ty B → NS B → o₀Ty B ∈ fvTy B
o₀-fv (arr ⋆ s t) (arr-wf ds _) _ with ⋆-var ds refl
... | j , refl = ∈-here j (fvTm t)
o₀-fv (arr (arr B s' t') s t) (arr-wf ds _) _ =
  ∈-++l (fvTy (arr B s' t')) (fvTm s ++ fvTm t) (o₀-fv (arr B s' t') (tm-ty ds) tt)

------------------------------------------------------------------------
-- Free variables under substitution.

fv-lookup : ∀ σ i {m} → i < lenₛ σ → m ∈ fvTm (lookupₛ σ i) → m ∈ fvSub σ
fv-lookup (σ ,ₛ t) i {m} (s≤s h) mem with ≤-case h
... | inj₁ q = ∈-++l (fvSub σ) (fvTm t)
                 (fv-lookup σ i q (subst (λ u → m ∈ fvTm u) (lookupₛ-there σ t i q) mem))
... | inj₂ q = ∈-++r (fvSub σ) (fvTm t) (subst (λ u → m ∈ fvTm u) (lookupₛ-here σ t i q) mem)

mutual
  fv-sub-ty : ∀ B ρ {m} → S.ScTy (lenₛ ρ) B → m ∈ fvTy (B [ ρ ]ty) → m ∈ fvSub ρ
  fv-sub-ty ⋆ ρ _ ()
  fv-sub-ty (arr B s t) ρ (hB , hs , ht) mem
    with ∈-++ (fvTy (B [ ρ ]ty)) (fvTm (s [ ρ ]tm) ++ fvTm (t [ ρ ]tm)) mem
  ... | inj₁ q = fv-sub-ty B ρ hB q
  ... | inj₂ q with ∈-++ (fvTm (s [ ρ ]tm)) (fvTm (t [ ρ ]tm)) q
  ...   | inj₁ r = fv-sub-tm s ρ hs r
  ...   | inj₂ r = fv-sub-tm t ρ ht r

  fv-sub-tm : ∀ u ρ {m} → S.ScTm (lenₛ ρ) u → m ∈ fvTm (u [ ρ ]tm) → m ∈ fvSub ρ
  fv-sub-tm (var i)     ρ h mem = fv-lookup ρ i (T→< i (lenₛ ρ) h) mem
  fv-sub-tm (coh _ _ σ) ρ h mem = fv-sub-sub σ ρ h mem
  fv-sub-tm (cst ())    ρ h mem

  fv-sub-sub : ∀ σ ρ {m} → S.ScSub (lenₛ ρ) σ → m ∈ fvSub (σ ∘ ρ) → m ∈ fvSub ρ
  fv-sub-sub ⟨⟩       ρ _ ()
  fv-sub-sub (σ ,ₛ u) ρ (hσ , hu) mem with ∈-++ (fvSub (σ ∘ ρ)) (fvTm (u [ ρ ]tm)) mem
  ... | inj₁ q = fv-sub-sub σ ρ hσ q
  ... | inj₂ q = fv-sub-tm u ρ hu q

------------------------------------------------------------------------
-- Every object of a valid coherence type's pasting context occurs in
-- its source or its target.

private
  snoc-l : ∀ {m} xs y → m ∈ xs → m ∈ snoc xs y
  snoc-l xs y = ∈-++l xs (y ∷ [])

  snoc-r : ∀ xs y → y ∈ snoc xs y
  snoc-r xs y = ∈-++r xs (y ∷ []) (∈-here y [])

  src-keep : ∀ Γ A B i {c} → c ∈ srcVars (suc i) Γ → c ∈ srcVars (suc i) (Γ ▸ A ▸ B)
  src-keep Γ A B i {c} h with suc i <ℕ suc (dim A)
  ... | true  = h
  ... | false = snoc-l {c} (snoc (srcVars (suc i) Γ) (len Γ)) (suc (len Γ))
                  (snoc-l {c} (srcVars (suc i) Γ) (len Γ) h)

-- Objects are in every positive-dimensional source.
obj-src : ∀ {Γ x A} → Γ ⊢ps x ∶ A → ∀ i c → lookup Γ c ≡ just ⋆ → c ∈ srcVars (suc i) Γ
obj-src pss i c eq with lookup-cases ε ⋆ c eq
... | inj₁ (refl , _) = ∈-here 0 []
... | inj₂ (() , _)
obj-src (pse {Γ} {x} {A} d) i c eq with lookup-cases (Γ ▸ A) (arr A (var x) (var (len Γ))) c eq
... | inj₁ (_ , ())
... | inj₂ (_ , eq') with lookup-cases Γ A c eq'
...   | inj₁ (refl , refl) = snoc-l {len Γ} (snoc (srcVars (suc i) Γ) (len Γ)) (suc (len Γ)) (snoc-r (srcVars (suc i) Γ) (len Γ))
...   | inj₂ (_ , eq'') = src-keep Γ A (arr A (var x) (var (len Γ))) i (obj-src d i c eq'')
obj-src (psd d) = obj-src d

private
  vtx≡0 : ∀ k → vtx k ≡ 0 → k ≡ 0
  vtx≡0 zero    _ = refl
  vtx≡0 (suc k) ()

  ⊆-elim : ∀ xs ys {m} → T (⊆? xs ys) → m ∈ xs → m ∈ ys
  ⊆-elim xs ys h q = all-elim (λ x → elem x ys) xs h q

objFv-chain : ∀ {Θ A s t x c} → Θ ⊢ps x ∶ ⋆ → dimCtx Θ ≤ 1 → Θ ⊢ty arr A s t → NS A →
              T (≈? (fvTmTy s A) (srcVars 0 Θ) ∧ ≈? (fvTmTy t A) (tgtVars 0 Θ)) →
              lookup Θ c ≡ just ⋆ → c ∈ fvTmTy s A
objFv-chain {A = A} {s} {t} {c = c} d le (arr-wf ds dt) ns op lc with ps-chain d le
... | k , refl , _ = ⊆-elim (srcVars 0 (chainC k)) (fvTmTy s A) sb in0
  where
  sa = ∧-fst op
  ta = ∧-snd {≈? (fvTmTy s A) (srcVars 0 (chainC k))} op
  sb = ∧-snd {⊆? (fvTmTy s A) (srcVars 0 (chainC k))} sa
  fA = o₀-fv A (tm-ty ds) ns
  z0 : o₀Ty A ≡ 0
  z0 = ∈-single (subst (o₀Ty A ∈_) (src-chain k)
         (⊆-elim (fvTmTy s A) (srcVars 0 (chainC k)) (∧-fst sa) (∈-++r (fvTm s) (fvTy A) fA)))
  zk : o₀Ty A ≡ vtx k
  zk = ∈-single (subst (o₀Ty A ∈_) (tgt-chain k)
         (⊆-elim (fvTmTy t A) (tgtVars 0 (chainC k)) (∧-fst ta) (∈-++r (fvTm t) (fvTy A) fA)))
  k0 : k ≡ 0
  k0 = vtx≡0 k (trans (sym zk) z0)
  c0 : c ≡ 0
  c0 with k0 | lookup-< {chainC k} lc
  ... | refl | s≤s z≤n = refl
  in0 : c ∈ srcVars 0 (chainC k)
  in0 = subst (c ∈_) (sym (src-chain k)) (subst (λ x → x ∈ 0 ∷ []) (sym c0) (∈-here 0 []))

objFv : ∀ {Θ A s t} → Θ ⊢ps → Θ ⊢ty arr A s t → NS A → T (cattSide Θ A s t) →
        ∀ c → lookup Θ c ≡ just ⋆ → (c ∈ fvTmTy s A) ⊎ (c ∈ fvTmTy t A)
objFv {Θ} {A} {s} {t} (ps d) a ns ok c lc with ∨-elim (isCoh Θ A s t) ok
... | inj₁ co =
  inj₁ (⊆-elim (downFrom (len Θ)) (fvTmTy s A)
          (∧-snd {⊆? (fvTmTy s A) (downFrom (len Θ))} (∧-fst co))
          (elem-downFrom (lookup-< {Θ} lc)))
... | inj₂ op with dimCtx Θ in eq
...   | suc (suc i) =
  inj₁ (⊆-elim (srcVars (suc i) Θ) (fvTmTy s A)
          (∧-snd {⊆? (fvTmTy s A) (srcVars (suc i) Θ)} (∧-fst op)) (obj-src d i c lc))
...   | zero     = inj₁ (objFv-chain d (subst (_≤ 1) (sym eq) z≤n) a ns op lc)
...   | suc zero = inj₁ (objFv-chain d (subst (_≤ 1) (sym eq) ≤-refl) a ns op lc)

------------------------------------------------------------------------
-- Monotone labellings and ranges.

Mono : Ctx → (Nat → List Nat) → Set
Mono Θ T = ∀ e c d → lookup Θ e ≡ just (arr ⋆ (var c) (var d)) → T c ⊑ T d

Rng : Ctx → (Nat → List Nat) → Ty → Nat → Set
Rng Θ T A m = (T (o₀Ty A) ⊑ T (o₀V Θ m)) × (T (o₁V Θ m) ⊑ T (o₁Ty A))

WfR : (Nat → List Nat) → Ty → Set
WfR T A = T (o₀Ty A) ⊑ T (o₁Ty A)

o-obj : ∀ {Θ m} → lookup Θ m ≡ just ⋆ → (o₀V Θ m ≡ m) × (o₁V Θ m ≡ m)
o-obj {Θ} {m} eq = cong (o₀M m) eq , cong (o₁M m) eq

o-arr : ∀ {Θ m B s t} → lookup Θ m ≡ just (arr B s t) →
        (o₀V Θ m ≡ o₀Ty (arr B s t)) × (o₁V Θ m ≡ o₁Ty (arr B s t))
o-arr {Θ} {m} eq = cong (o₀M m) eq , cong (o₁M m) eq

mono-restrict : ∀ {Γ A B T} → Mono (Γ ▸ A ▸ B) T → Mono Γ T
mono-restrict {Γ} {A} {B} mo e c d eq = mo e c d (lookup-wk {Γ ▸ A} {B} (lookup-wk {Γ} {A} eq))

-- The objects of a chain lie between its ends.
chain-bdry : ∀ k T → Mono (chainC k) T → ∀ c → lookup (chainC k) c ≡ just ⋆ →
             (T 0 ⊑ T c) × (T c ⊑ T (vtx k))
chain-bdry zero T mo c eq with lookup-cases ε ⋆ c eq
... | inj₁ (refl , _) = ⊑-refl , ⊑-refl
... | inj₂ (() , _)
chain-bdry (suc k) T mo c eq with lookup-cases (chainC k ▸ ⋆) (arr ⋆ (var (vtx k)) (var (vtx (suc k)))) c eq
... | inj₁ (_ , ())
... | inj₂ (_ , eq') with lookup-cases (chainC k) ⋆ c eq'
...   | inj₁ (refl , _) =
        subst (λ n → T 0 ⊑ T n) (sym (len-chain k)) (⊑-trans (fst ih) step) ,
        subst (λ n → T n ⊑ T (vtx (suc k))) (sym (len-chain k)) ⊑-refl
  where
  ih = chain-bdry k T (mono-restrict mo) (vtx k) (lookup-vtx k k ≤-refl)
  step : T (vtx k) ⊑ T (vtx (suc k))
  step = mo (edge (suc k)) (vtx k) (vtx (suc k)) (lookup-edge (suc k) k ≤-refl)
...   | inj₂ (_ , eq'') =
        fst ih , ⊑-trans (snd ih) (mo (edge (suc k)) (vtx k) (vtx (suc k)) (lookup-edge (suc k) k ≤-refl))
  where
  ih = chain-bdry k T (mono-restrict mo) c eq''

-- Variables of a pasting context, through their types.
private
  isVar : ∀ {Θ B} s → VarIs Θ B s → Σ Nat λ c → (s ≡ var c) × (lookup Θ c ≡ just B)
  isVar (var c) h = c , refl , h

tyRange : ∀ {Θ} T → Good Θ → Mono Θ T → ∀ A {j} → lookup Θ j ≡ just A → NS A →
          WfR T A × (∀ m → m ∈ fvTy A → Rng Θ T A m)
tyRange {Θ} T g mo (arr B s t) {j} lj _ with g j _ lj
... | vs , vt with isVar s vs | isVar t vt
...   | c , refl , lc | d , refl , ld = go B lc ld lj
  where
  go : ∀ B → lookup Θ c ≡ just B → lookup Θ d ≡ just B → lookup Θ j ≡ just (arr B (var c) (var d)) →
       WfR T (arr B (var c) (var d)) × (∀ m → m ∈ fvTy (arr B (var c) (var d)) → Rng Θ T (arr B (var c) (var d)) m)
  go ⋆ lc ld lj = mo j c d lj , pick
    where
    cd = mo j c d lj
    pick : ∀ m → m ∈ c ∷ d ∷ [] → Rng Θ T (arr ⋆ (var c) (var d)) m
    pick m mem with ∨-elim (m ==ℕ c) mem
    ... | inj₁ q rewrite ==ℕ-sound m c q =
          subst (λ x → T c ⊑ T x) (sym (fst (o-obj {Θ} lc))) ⊑-refl ,
          subst (λ x → T x ⊑ T d) (sym (snd (o-obj {Θ} lc))) cd
    ... | inj₂ q rewrite ∈-single {m} {d} q =
          subst (λ x → T c ⊑ T x) (sym (fst (o-obj {Θ} ld))) cd ,
          subst (λ x → T x ⊑ T d) (sym (snd (o-obj {Θ} ld))) ⊑-refl
  go (arr B₀ s₀ t₀) lc ld lj with tyRange T g mo (arr B₀ s₀ t₀) lc tt
  ... | wf , r = wf , pick
    where
    B' = arr B₀ s₀ t₀
    pick : ∀ m → m ∈ fvTy B' ++ (c ∷ d ∷ []) → Rng Θ T (arr B' (var c) (var d)) m
    pick m mem with ∈-++ (fvTy B') (c ∷ d ∷ []) mem
    ... | inj₁ q = r m q
    ... | inj₂ q with ∨-elim (m ==ℕ c) q
    ...   | inj₁ q' rewrite ==ℕ-sound m c q' =
            subst (λ x → T (o₀Ty B') ⊑ T x) (sym (fst (o-arr {Θ} lc))) ⊑-refl ,
            subst (λ x → T x ⊑ T (o₁Ty B')) (sym (snd (o-arr {Θ} lc))) ⊑-refl
    ...   | inj₂ q' rewrite ∈-single {m} {d} q' =
            subst (λ x → T (o₀Ty B') ⊑ T x) (sym (fst (o-arr {Θ} ld))) ⊑-refl ,
            subst (λ x → T x ⊑ T (o₁Ty B')) (sym (snd (o-arr {Θ} ld))) ⊑-refl

------------------------------------------------------------------------
-- The range and boundary lemmas.

private
  lookupₛ-wk : ∀ {Θ Θ'' ρ u c} → Θ ⊢sub ρ ∶ Θ'' → c < len Θ'' → lookupₛ (ρ ,ₛ u) c ≡ lookupₛ ρ c
  lookupₛ-wk {ρ = ρ} {u} {c} s h = lookupₛ-there ρ u c (subst (c <_) (sym (snd (S.sub-sc closed s))) h)

  lookupₛ-top : ∀ {Θ Θ'' ρ u} → Θ ⊢sub ρ ∶ Θ'' → lookupₛ (ρ ,ₛ u) (len Θ'') ≡ u
  lookupₛ-top {Θ'' = Θ''} {ρ} {u} s = lookupₛ-here ρ u (len Θ'') (sym (snd (S.sub-sc closed s)))

  subst₂ : ∀ {A : Set} (P : A → A → Set) {x x' y y'} → x ≡ x' → y ≡ y' → P x y → P x' y'
  subst₂ P refl refl p = p

mutual
  range : ∀ {Θ} T → Good Θ → Mono Θ T → ∀ t {A} → Θ ⊢tm t ∶ A → NS A →
          WfR T A × (∀ m → m ∈ fvTmTy t A → Rng Θ T A m)
  range {Θ} T g mo (var j) {arr B s t} (var-wf w lj) ns =
    fst tr , pick
    where
    tr = tyRange T g mo (arr B s t) lj ns
    pick : ∀ m → m ∈ j ∷ fvTy (arr B s t) → Rng Θ T (arr B s t) m
    pick m mem with ∨-elim (m ==ℕ j) mem
    ... | inj₁ q rewrite ==ℕ-sound m j q =
          subst (λ x → T (o₀Ty (arr B s t)) ⊑ T x) (sym (fst (o-arr {Θ} lj))) ⊑-refl ,
          subst (λ x → T x ⊑ T (o₁Ty (arr B s t))) (sym (snd (o-arr {Θ} lj))) ⊑-refl
    ... | inj₂ q = snd tr m q
  range {Θ} T g mo (coh Θ' (arr A' s' t') ρ) (coh-wf (ps p₀) w a ok s) ns = wf , cover
    where
    A'' = arr A' s' t'
    A   = A'' [ ρ ]ty
    T' : Nat → List Nat
    T' y = T (vi (lookupₛ ρ y))
    mo' : Mono Θ' T'
    mo' = monoS T g mo ρ s w
    bd : ∀ c → lookup Θ' c ≡ just ⋆ → (T' (o₀Ty A'') ⊑ T' c) × (T' c ⊑ T' (o₁Ty A''))
    bd = bdry T' (ps p₀) (fst (good p₀)) mo' A' s' t' a ok
    lo-eq : T (o₀Ty A) ≡ T' (o₀Ty A'')
    lo-eq = cong T (o₀-sub A'' ρ a tt)
    hi-eq : T (o₁Ty A) ≡ T' (o₁Ty A'')
    hi-eq = cong T (o₁-sub A'' ρ a tt)
    H : ∀ c → lookup Θ' c ≡ just ⋆ →
        (T (o₀Ty A) ⊑ T (vi (lookupₛ ρ c))) × (T (vi (lookupₛ ρ c)) ⊑ T (o₁Ty A))
    H c lc = subst (_⊑ T' c) (sym lo-eq) (fst (bd c lc)) ,
             subst (T' c ⊑_) (sym hi-eq) (snd (bd c lc))
    wf : WfR T A
    wf = ⊑-trans (fst (H 0 (ps-0 p₀))) (snd (H 0 (ps-0 p₀)))
    cs : ∀ m → m ∈ fvSub ρ → Rng Θ T A m
    cs = rangeS T g mo ρ s w (T (o₀Ty A)) (T (o₁Ty A)) H
    scA : S.ScTy (lenₛ ρ) A''
    scA = subst (λ n → S.ScTy n A'') (sym (snd (S.sub-sc closed s))) (S.ty-sc closed a)
    cover : ∀ m → m ∈ fvSub ρ ++ fvTy A → Rng Θ T A m
    cover m mem with ∈-++ (fvSub ρ) (fvTy A) mem
    ... | inj₁ q = cs m q
    ... | inj₂ q = cs m (fv-sub-ty A'' ρ scA q)
  range T g mo (cst ()) _ _

  rangeS : ∀ {Θ Θ''} T → Good Θ → Mono Θ T → ∀ ρ → Θ ⊢sub ρ ∶ Θ'' → Θ'' ⊢ctx → ∀ lo hi →
           (∀ c → lookup Θ'' c ≡ just ⋆ → (lo ⊑ T (vi (lookupₛ ρ c))) × (T (vi (lookupₛ ρ c)) ⊑ hi)) →
           ∀ m → m ∈ fvSub ρ → (lo ⊑ T (o₀V Θ m)) × (T (o₁V Θ m) ⊑ hi)
  rangeS T g mo ⟨⟩ _ _ lo hi H m ()
  rangeS {Θ} {Θ'' ▸ B} T g mo (ρ ,ₛ u) (,-wf s du) (▸-wf w b) lo hi H m mem
    with ∈-++ (fvSub ρ) (fvTm u) mem
  ... | inj₁ q = rangeS T g mo ρ s w lo hi H' m q
    where
    H' : ∀ c → lookup Θ'' c ≡ just ⋆ → (lo ⊑ T (vi (lookupₛ ρ c))) × (T (vi (lookupₛ ρ c)) ⊑ hi)
    H' c lc = subst (λ x → (lo ⊑ T (vi x)) × (T (vi x) ⊑ hi)) (lookupₛ-wk {u = u} s (lookup-< {Θ''} lc))
                    (H c (lookup-wk {Θ''} {B} lc))
  ... | inj₂ q = entry B b du H q
    where
    entry : ∀ B → Θ'' ⊢ty B → Θ ⊢tm u ∶ B [ ρ ]ty →
            (∀ c → lookup (Θ'' ▸ B) c ≡ just ⋆ →
               (lo ⊑ T (vi (lookupₛ (ρ ,ₛ u) c))) × (T (vi (lookupₛ (ρ ,ₛ u) c)) ⊑ hi)) →
            m ∈ fvTm u → (lo ⊑ T (o₀V Θ m)) × (T (o₁V Θ m) ⊑ hi)
    entry ⋆ _ du H q with ⋆-var du refl
    ... | j , refl with du
    ...   | var-wf _ lj rewrite ∈-single {m} {j} q =
            let h = H (len Θ'') (lookup-here Θ'' ⋆ (len Θ'') refl)
                e = cong (λ x → T (vi x)) (lookupₛ-top {u = var j} s) in
            subst (lo ⊑_) (trans e (cong T (sym (fst (o-obj {Θ} lj))))) (fst h) ,
            subst (_⊑ hi) (trans e (cong T (sym (snd (o-obj {Θ} lj))))) (snd h)
    entry (arr B₀ s₀ t₀) b du H q =
      ⊑-trans (fst ho) (subst (_⊑ T (o₀V Θ m)) (cong T (o₀-sub (arr B₀ s₀ t₀) ρ b tt)) (fst rm)) ,
      ⊑-trans (subst (T (o₁V Θ m) ⊑_) (cong T (o₁-sub (arr B₀ s₀ t₀) ρ b tt)) (snd rm)) (snd hi')
      where
      B' = arr B₀ s₀ t₀
      rm = snd (range T g mo u du tt) m (∈-++l (fvTm u) (fvTy (B' [ ρ ]ty)) q)
      at : ∀ c → lookup Θ'' c ≡ just ⋆ → (lo ⊑ T (vi (lookupₛ ρ c))) × (T (vi (lookupₛ ρ c)) ⊑ hi)
      at c lc = subst (λ x → (lo ⊑ T (vi x)) × (T (vi x) ⊑ hi)) (lookupₛ-wk {u = u} s (lookup-< {Θ''} lc))
                      (H c (lookup-wk {Θ''} {B'} lc))
      ho  = at (o₀Ty B') (o₀-obj B' b tt)
      hi' = at (o₁Ty B') (o₁-obj B' b tt)

  monoS : ∀ {Θ Θ''} T → Good Θ → Mono Θ T → ∀ ρ → Θ ⊢sub ρ ∶ Θ'' → Θ'' ⊢ctx →
          Mono Θ'' (λ y → T (vi (lookupₛ ρ y)))
  monoS T g mo ⟨⟩ (⟨⟩-wf _) _ e c d ()
  monoS {Θ} {Θ'' ▸ B} T g mo (ρ ,ₛ u) (,-wf s du) (▸-wf w b) e c d le with lookup-cases Θ'' B e le
  ... | inj₁ (refl , refl) with b
  ...   | arr-wf (var-wf _ lc) (var-wf _ ld) =
          subst₂ (λ x y → T (vi x) ⊑ T (vi y))
            (sym (lookupₛ-wk {u = u} s (lookup-< {Θ''} lc))) (sym (lookupₛ-wk {u = u} s (lookup-< {Θ''} ld)))
            (fst (range T g mo u du tt))
  monoS {Θ} {Θ'' ▸ B} T g mo (ρ ,ₛ u) (,-wf s du) (▸-wf w b) e c d le | inj₂ (_ , le') with lookup-wf w le'
  ... | arr-wf (var-wf _ lc) (var-wf _ ld) =
          subst₂ (λ x y → T (vi x) ⊑ T (vi y))
            (sym (lookupₛ-wk {u = u} s (lookup-< {Θ''} lc))) (sym (lookupₛ-wk {u = u} s (lookup-< {Θ''} ld)))
            (monoS T g mo ρ s w e c d le')

  bdry : ∀ {Θ} L → Θ ⊢ps → Good Θ → Mono Θ L → ∀ A s t → Θ ⊢ty arr A s t → T (cattSide Θ A s t) →
         ∀ c → lookup Θ c ≡ just ⋆ → (L (o₀Ty (arr A s t)) ⊑ L c) × (L c ⊑ L (o₁Ty (arr A s t)))
  bdry L p g mo ⋆ s t (arr-wf ds dt) ok c lc with ⋆-var ds refl | ⋆-var dt refl
  ... | j , refl | j' , refl with chain-side p ok
  ...   | k , refl , refl , refl = chain-bdry k L mo c lc
  bdry {Θ} L p g mo (arr A₀ u v) s t a@(arr-wf ds dt) ok c lc with objFv p a tt ok c lc
  ... | inj₁ q = let r = snd (range L g mo s ds tt) c q in
                 subst (λ x → L (o₀Ty (arr A₀ u v)) ⊑ L x) (fst (o-obj {Θ} lc)) (fst r) ,
                 subst (λ x → L x ⊑ L (o₁Ty (arr A₀ u v))) (snd (o-obj {Θ} lc)) (snd r)
  ... | inj₂ q = let r = snd (range L g mo t dt tt) c q in
                 subst (λ x → L (o₀Ty (arr A₀ u v)) ⊑ L x) (fst (o-obj {Θ} lc)) (fst r) ,
                 subst (λ x → L x ⊑ L (o₁Ty (arr A₀ u v))) (snd (o-obj {Θ} lc)) (snd r)
