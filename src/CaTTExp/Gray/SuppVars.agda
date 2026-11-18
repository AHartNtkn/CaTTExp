------------------------------------------------------------------------
-- Closed supports contain only free variables.
--
--   supp-vars : Inv Γ → Γ ⊢tm t ∶ A → x ∈ supp t A → Reach k x y →
--               e ∈ y → e ∈ Var(t : A)
--
-- for every context Γ whose types are variable towers (every pasting
-- context, Gray.PsFacts), and every derivable t : A of two-tier L over a
-- closed signature. Var(t : A) = FV(t) ∪ FV(A) (Syntax.fvTmTy), and
-- Reach is the face order of Gray.DownAgree, so every entry of every
-- tuple of ↓supp(t : A) is a variable of t : A. This is the "⇒" half of
-- single-hom conservativity (notes/conjectures/single-hom-conservativity.md);
-- it holds in any number of homs.
--
-- Two steps:
--   * entries of supp(t : A) are variables of t : A (syntactic:
--     `top-fv`, `suppTy-fv`);
--   * Var(t : A) is closed under taking the variables of a variable's
--     type, for derivable t : A (`tm-dc`), as in CaTT; the faces of a
--     cell are variables of its type (`bd-var`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.SuppVars (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.DownAgree 𝕊
open import CaTTExp.Gray.Graded 𝕊
open import CaTTExp.Gray.Typing 𝕊
import CaTTExp.Subst 𝕊 graySide as S

------------------------------------------------------------------------
-- Lists.

private
  ∈-++l : ∀ {e} xs {ys} → e ∈ᴺ xs → e ∈ᴺ (xs ++ ys)
  ∈-++l xs m = any-++l m

  ∈-++r : ∀ {e} xs {ys} → e ∈ᴺ ys → e ∈ᴺ (xs ++ ys)
  ∈-++r xs m = any-++r xs m

  ⊎-case : ∀ {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
  ⊎-case (inj₁ a) f g = f a
  ⊎-case (inj₂ b) f g = g b

  just-inj' : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj' refl = refl

  nth-mem : ∀ w L {y} → y ∈L nth w L → Σ TSet λ X → Any (X ≡_) L × y ∈L X
  nth-mem w       []      ()
  nth-mem zero    (X ∷ L) m = X , here refl , m
  nth-mem (suc w) (X ∷ L) m with nth-mem w L m
  ... | X' , mX , my = X' , there mX , my

  Ftuple-ent : ∀ tops c {x e} → x ∈L Ftuple tops c → e ∈ᴺ x →
               Σ TSet λ X → Any (X ≡_) tops × Σ Tuple λ y → y ∈L X × e ∈ᴺ y
  Ftuple-ent tops []       (here refl) ()
  Ftuple-ent tops []       (there ())  _
  Ftuple-ent tops (w ∷ ws) mx me with prodT⇒ (nth w tops) (Ftuple tops ws) mx
  ... | y , z , refl , my , mz with any-++⁻ y me
  ...   | inj₁ a with nth-mem w tops my
  ...     | X , mX , my' = X , mX , y , my' , a
  Ftuple-ent tops (w ∷ ws) mx me | y , z , refl , my , mz | inj₂ b = Ftuple-ent tops ws mz b

------------------------------------------------------------------------
-- Entries of supports are variables (no typing needed).

mutual
  top-fv : ∀ t {x e} → x ∈L topS t → e ∈ᴺ x → e ∈ᴺ fvTm t
  top-fv (var v)               (here refl) (here refl) = here refl
  top-fv (var v)               (here refl) (there ())
  top-fv (var v)               (there ())  _
  top-fv (cst _)               ()          _
  top-fv (coh Θ ⋆ ρ)           ()          _
  top-fv (coh Θ (arr A t u) ρ) {x} mx me
    with any-witness (any-cm⁻ (Ftuple (topsSub ρ)) C (subst (Any _) (cm≡ (Ftuple (topsSub ρ)) C) mx))
    where C = if cohCase Θ A t u then [] else topT (homs Θ)
  ... | c , _ , mxc with Ftuple-ent (topsSub ρ) c mxc me
  ...   | X , mX , y , my , ey = tops-fv ρ mX my ey

  tops-fv : ∀ ρ {X y e} → Any (X ≡_) (topsSub ρ) → y ∈L X → e ∈ᴺ y → e ∈ᴺ fvSub ρ
  tops-fv ⟨⟩       ()        _  _
  tops-fv (ρ ,ₛ t) mX my ey with any-++⁻ (topsSub ρ) mX
  ... | inj₁ a          = ∈-++l (fvSub ρ) (tops-fv ρ a my ey)
  ... | inj₂ (here refl) = ∈-++r (fvSub ρ) (top-fv t my ey)
  ... | inj₂ (there ())

suppTy-fv : ∀ A {x e} → x ∈L suppTy A → e ∈ᴺ x → e ∈ᴺ fvTy A
suppTy-fv ⋆                      () _
suppTy-fv (arr ⋆ _ _)            () _
suppTy-fv (arr (arr B s s') t u) mx me =
  ⊎-case (any-++⁻ (suppTy (arr B s s')) mx)
    (λ a → ∈-++l (fvTy (arr B s s')) (suppTy-fv (arr B s s') a me))
    (λ b → ⊎-case (any-++⁻ (topS t) b)
      (λ c → ∈-++r (fvTy (arr B s s')) (∈-++l (fvTm t) (top-fv t c me)))
      (λ d → ∈-++r (fvTy (arr B s s')) (∈-++r (fvTm t) (top-fv u d me))))

supp-fv : ∀ t A {x e} → x ∈L supp t A → e ∈ᴺ x → e ∈ᴺ fvTmTy t A
supp-fv t A mx me with any-++⁻ (topS t) mx
... | inj₁ a = ∈-++l (fvTm t) (top-fv t a me)
... | inj₂ b = ∈-++r (fvTm t) (suppTy-fv A b me)

------------------------------------------------------------------------
-- Variables under substitution, and scoping.

mutual
  fv-tm[] : ∀ t σ {v} → v ∈ᴺ fvTm (t [ σ ]tm) → Σ Nat λ w → w ∈ᴺ fvTm t × v ∈ᴺ fvTm (lookupₛ σ w)
  fv-tm[] (var i)     σ m = i , here refl , m
  fv-tm[] (coh Δ A ρ) σ m = fv-∘ ρ σ m
  fv-tm[] (cst _)     σ ()

  fv-∘ : ∀ ρ σ {v} → v ∈ᴺ fvSub (ρ ∘ σ) → Σ Nat λ w → w ∈ᴺ fvSub ρ × v ∈ᴺ fvTm (lookupₛ σ w)
  fv-∘ ⟨⟩       σ ()
  fv-∘ (ρ ,ₛ t) σ m with any-++⁻ (fvSub (ρ ∘ σ)) m
  ... | inj₁ a with fv-∘ ρ σ a
  ...   | w , mw , mv = w , ∈-++l (fvSub ρ) mw , mv
  fv-∘ (ρ ,ₛ t) σ m | inj₂ b with fv-tm[] t σ b
  ...   | w , mw , mv = w , ∈-++r (fvSub ρ) mw , mv

fv-ty[] : ∀ A σ {v} → v ∈ᴺ fvTy (A [ σ ]ty) → Σ Nat λ w → w ∈ᴺ fvTy A × v ∈ᴺ fvTm (lookupₛ σ w)
fv-ty[] ⋆           σ ()
fv-ty[] (arr A t u) σ m with any-++⁻ (fvTy (A [ σ ]ty)) m
... | inj₁ a with fv-ty[] A σ a
...   | w , mw , mv = w , ∈-++l (fvTy A) mw , mv
fv-ty[] (arr A t u) σ m | inj₂ b with any-++⁻ (fvTm (t [ σ ]tm)) b
...   | inj₁ c with fv-tm[] t σ c
...     | w , mw , mv = w , ∈-++r (fvTy A) (∈-++l (fvTm t) mw) , mv
fv-ty[] (arr A t u) σ m | inj₂ b | inj₂ d with fv-tm[] u σ d
...     | w , mw , mv = w , ∈-++r (fvTy A) (∈-++r (fvTm t) mw) , mv

private
  lt-ne' : ∀ i n → T (i <ℕ n) → (i ==ℕ n) ≡ false
  lt-ne' zero    (suc n) _ = refl
  lt-ne' (suc i) (suc n) p = lt-ne' i n p

  lt-suc-ne : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  lt-suc-ne zero    zero    _ ()
  lt-suc-ne zero    (suc n) _ _ = tt
  lt-suc-ne (suc i) (suc n) p q = lt-suc-ne i n p q

lookup-in : ∀ σ w {v} → T (w <ℕ lenₛ σ) → v ∈ᴺ fvTm (lookupₛ σ w) → v ∈ᴺ fvSub σ
lookup-in (σ ,ₛ t) w {v} p m with w ==ℕ lenₛ σ in q
... | true  = ∈-++r (fvSub σ) m
... | false = ∈-++l (fvSub σ) (lookup-in σ w (lt-suc-ne w (lenₛ σ) p q) m)

mutual
  sc-fv : ∀ n t {w} → S.ScTm n t → w ∈ᴺ fvTm t → T (w <ℕ n)
  sc-fv n (var i)     h (here refl) = h
  sc-fv n (var i)     h (there ())
  sc-fv n (coh _ _ σ) h m           = sc-fvs n σ h m
  sc-fv n (cst _)     h ()

  sc-fvs : ∀ n σ {w} → S.ScSub n σ → w ∈ᴺ fvSub σ → T (w <ℕ n)
  sc-fvs n ⟨⟩       _        ()
  sc-fvs n (σ ,ₛ t) (hσ , ht) m with any-++⁻ (fvSub σ) m
  ... | inj₁ a = sc-fvs n σ hσ a
  ... | inj₂ b = sc-fv n t ht b

sc-fvTy : ∀ n A {w} → S.ScTy n A → w ∈ᴺ fvTy A → T (w <ℕ n)
sc-fvTy n ⋆           _           ()
sc-fvTy n (arr A t u) (ha , ht , hu) m with any-++⁻ (fvTy A) m
... | inj₁ a = sc-fvTy n A ha a
... | inj₂ b with any-++⁻ (fvTm t) b
...   | inj₁ c = sc-fv n t ht c
...   | inj₂ d = sc-fv n u hu d

------------------------------------------------------------------------
-- Var(t : A) is closed under the variables of a variable's type.

module _ (closed : S.Closed) {Γ : Ctx} (inv : Inv Γ) where

  -- Inside a variable tower.
  tow-dc : ∀ C → VT Γ C → ∀ {v D u} → v ∈ᴺ fvTy C → lookup Γ v ≡ just D → u ∈ᴺ fvTy D → u ∈ᴺ fvTy C
  tow-dc ⋆ _ ()
  tow-dc (arr B .(var i) .(var j)) (i , j , refl , refl , li , lj) {v} mv eD mu
    with any-++⁻ (fvTy B) mv
  ... | inj₁ a = ∈-++l (fvTy B) (tow-dc B (inv i B li) a eD mu)
  ... | inj₂ (here refl)         = ∈-++l (fvTy B) (subst (λ X → _ ∈ᴺ fvTy X) (just-inj' (trans (sym eD) li)) mu)
  ... | inj₂ (there (here refl)) = ∈-++l (fvTy B) (subst (λ X → _ ∈ᴺ fvTy X) (just-inj' (trans (sym eD) lj)) mu)
  ... | inj₂ (there (there ()))

  mutual
    tm-dc : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ {v D u} → v ∈ᴺ fvTmTy t A → lookup Γ v ≡ just D →
            u ∈ᴺ fvTy D → u ∈ᴺ fvTmTy t A
    tm-dc (var-wf {i} {C} w eq) mv eD mu with any-++⁻ (i ∷ []) mv
    ... | inj₁ (here refl) = ∈-++r (i ∷ []) (subst (λ X → _ ∈ᴺ fvTy X) (just-inj' (trans (sym eD) eq)) mu)
    ... | inj₁ (there ())
    ... | inj₂ b = ∈-++r (i ∷ []) (tow-dc C (inv i C eq) b eD mu)
    tm-dc (coh-wf {Δ} {A'} {t'} {u'} {σ} _ cw ty _ sσ) mv eD mu with any-++⁻ (fvSub σ) mv
    ... | inj₁ a = ∈-++l (fvSub σ) (sub-dc cw sσ a eD mu)
    ... | inj₂ b with fv-ty[] (arr A' t' u') σ b
    ...   | w , mw , mv' =
      ∈-++l (fvSub σ) (sub-dc cw sσ (lookup-in σ w bnd mv') eD mu)
      where
      bnd : T (w <ℕ lenₛ σ)
      bnd = subst (λ n → T (w <ℕ n)) (sym (snd (S.sub-sc closed sσ)))
              (sc-fvTy (len Δ) (arr A' t' u') (S.ty-sc closed ty) mw)
    tm-dc (cst-wf {k} w v) mv eD mu with sc-fvTy 0 (ty k) (closed k) mv
    ... | ()

    sub-dc : ∀ {Δ σ} → Δ ⊢ctx → Γ ⊢sub σ ∶ Δ → ∀ {v D u} → v ∈ᴺ fvSub σ → lookup Γ v ≡ just D →
             u ∈ᴺ fvTy D → u ∈ᴺ fvSub σ
    sub-dc _ (⟨⟩-wf _) ()
    sub-dc (▸-wf cw b) (,-wf {σ} {Δ} {t} {A} sd d) mv eD mu with any-++⁻ (fvSub σ) mv
    ... | inj₁ a = ∈-++l (fvSub σ) (sub-dc cw sd a eD mu)
    ... | inj₂ c with any-++⁻ (fvTm t) (tm-dc d (∈-++l (fvTm t) c) eD mu)
    ...   | inj₁ e = ∈-++r (fvSub σ) e
    ...   | inj₂ f with fv-ty[] A σ f
    ...     | w , mw , mu' = ∈-++l (fvSub σ) (lookup-in σ w bnd mu')
      where
      bnd : T (w <ℕ lenₛ σ)
      bnd = subst (λ n → T (w <ℕ n)) (sym (snd (S.sub-sc closed sd)))
              (sc-fvTy (len Δ) A (S.ty-sc closed b) mw)

  ----------------------------------------------------------------------
  -- Faces of a cell are variables of its type.

  bd-var : ∀ {w b} → b ∈ᴺ bdEl (cells Γ) w → Σ Ty λ D → (lookup Γ w ≡ just D) × (b ∈ᴺ fvTy D)
  bd-var {w} {b} mb with findEl w (cells Γ) in fe
  ... | nothing = ⊥-elim (none mb)
    where
    none : b ∈ᴺ [] → ⊥
    none ()
  ... | just c with elAt-just (objs Γ) Γ w (trans (sym (findEl-cells (objs Γ) Γ w)) fe)
  ...   | D , eL , k , eH , refl = D , eL , shape D eL mb
    where
    shape : ∀ D → lookup Γ w ≡ just D →
            b ∈ᴺ (if (dim D ∸ 1) ==ℕ 0 then [] else (fst (elBdry D) ∷ snd (elBdry D) ∷ [])) →
            b ∈ᴺ fvTy D
    shape ⋆ _ ()
    shape (arr ⋆ _ _) _ ()
    shape (arr (arr X s0 t0) a a') eL' m with inv w _ eL'
    ... | i , j , refl , refl , _ , _ with m
    ...   | here refl         = ∈-++r (fvTy (arr X s0 t0)) (here refl)
    ...   | there (here refl) = ∈-++r (fvTy (arr X s0 t0)) (there (here refl))
    ...   | there (there ())

  ----------------------------------------------------------------------
  -- The theorem.

  open Faces (cells Γ)

  private
    step-ok : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ {x y} → Step x y →
              (∀ {e} → e ∈ᴺ x → e ∈ᴺ fvTmTy t A) → ∀ {e} → e ∈ᴺ y → e ∈ᴺ fvTmTy t A
    step-ok d (sh mb) ok (here refl) with bd-var mb
    ... | D , eL , mbD = tm-dc d (ok (here refl)) eL mbD
    step-ok d (sh mb) ok (there m) = ok (there m)
    step-ok d (st s)  ok (here refl) = ok (here refl)
    step-ok d (st s)  ok (there m) = step-ok d s (λ m' → ok (there m')) m

    reach-ok : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ {k x y} → Reach k x y →
               (∀ {e} → e ∈ᴺ x → e ∈ᴺ fvTmTy t A) → ∀ {e} → e ∈ᴺ y → e ∈ᴺ fvTmTy t A
    reach-ok d done       ok = ok
    reach-ok d (step s r) ok = reach-ok d r (step-ok d s ok)

  -- Every entry of every tuple of ↓supp(t : A) is a variable of t : A.
  supp-vars : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ {x k y} → x ∈L supp t A → Reach k x y →
              ∀ {e} → e ∈ᴺ y → e ∈ᴺ fvTmTy t A
  supp-vars {t} {A} d mx r = reach-ok d r (supp-fv t A mx)

  -- The same, for the bounded face order that the side condition uses.
  supp-vars-leq : ∀ {t A} → Γ ⊢tm t ∶ A → ∀ n {x y} → x ∈L supp t A → T (leqT (cells Γ) n y x) →
                  ∀ {e} → e ∈ᴺ y → e ∈ᴺ fvTmTy t A
  supp-vars-leq d n {x} {y} mx q with pw⇒reach (leqT⇒ n y x q)
  ... | k , r = supp-vars d mx r
