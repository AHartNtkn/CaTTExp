------------------------------------------------------------------------
-- D7e: substitution on the biclosed syntax, and stability of the type
-- checker under well-typed substitution.
--
-- A substitution σ assigns a formula to every object variable and a
-- term to every context variable.  Γ ⊢ σ ∶ Δ says that σ sends each
-- entry of Δ to a term of Γ of the substituted type.
--
-- Main result (no postulates):
--   sub-infer : Γ ⊢ σ ∶ Δ → infer Δ x ≡ just A → infer Γ (x [σ]) ≡ just (A [σ])
--   sub-wf    : Γ ⊢ σ ∶ Δ → T (wf Δ A) → T (wf Γ (A [σ]))
-- and composition of substitutions.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Subst where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.SubstDef public
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.TemplatesTyped
  using (T→≡; eqTy-false; map-++)
open import CaTTExp.Gray.Biclosed.Scope
  using (scY; All; []; _∷_; inst-sY; module TmplScope)

-- Γ ⊢ σ ∶ Δ
record _⊢_∶_ (Γ : Ctx) (σ : Sub) (Δ : Ctx) : Set where
  constructor ⊢in
  field
    app : ∀ i A → lookup Δ i ≡ just A → infer Γ (tm σ i) ≡ just (sY σ A)
open _⊢_∶_ public

------------------------------------------------------------------------
-- Inversion helpers

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

if-inv : ∀ {A : Set} b {x : Maybe A} {y : A} →
         (if b then x else nothing) ≡ just y → T b × x ≡ just y
if-inv true  e = tt , e
if-inv false ()

bind-inv : ∀ {A B : Set} (m : Maybe A) {k : A → Maybe B} {y : B} →
           (m >>= k) ≡ just y → Σ A (λ a → m ≡ just a × k a ≡ just y)
bind-inv (just a) e = a , refl , e
bind-inv nothing ()

≡→T : ∀ {b} → b ≡ true → T b
≡→T refl = tt

comp-inv : ∀ Δ f gs {A} → infer Δ (comp f gs) ≡ just A →
  Σ CTy (λ tf → Σ (List CTy) (λ tgs →
    infer Δ f ≡ just tf × inferL Δ gs ≡ just tgs × compTy f gs tf tgs ≡ just A))
comp-inv Δ f gs e with infer Δ f | inferL Δ gs
... | just tf | just tgs = tf , tgs , refl , refl , e
... | just _  | nothing  = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()
... | nothing | _        = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()

glue-inv : ∀ Δ am x ap {A} → infer Δ (glue am x ap) ≡ just A →
  Σ CTy (λ ta → Σ CTy (λ tb → Σ CTy (λ tx →
    infer Δ am ≡ just ta × infer Δ ap ≡ just tb × infer Δ x ≡ just tx ×
    glueTop am ap ta tb tx ≡ just A)))
glue-inv Δ am x ap e with infer Δ am | infer Δ ap | infer Δ x
... | just ta | just tb | just tx = ta , tb , tx , refl , refl , refl , e
... | nothing | _       | _       = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()
... | just _  | nothing | _       = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()
... | just _  | just _  | nothing = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()

cons-inv : ∀ Δ t ts {As} → inferL Δ (t ∷ ts) ≡ just As →
  Σ CTy (λ A → Σ (List CTy) (λ Bs →
    infer Δ t ≡ just A × inferL Δ ts ≡ just Bs × As ≡ A ∷ Bs))
cons-inv Δ t ts e with infer Δ t | inferL Δ ts
... | just A  | just Bs = A , Bs , refl , refl , sym (just-inj e)
... | just _  | nothing = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()
... | nothing | _       = ⊥-elim (nj e) where
  nj : ∀ {X : Set} {y : X} → nothing ≡ just y → ⊥
  nj ()

------------------------------------------------------------------------
-- compTy on an operation, as a plain function of its tests

sel : Bool → Bool → Maybe (Σ Nat (λ _ → CTy)) → Tm → List Tm → MTy → List MTy → Maybe CTy
sel true  _     _               f gs Mf ms = mapM op (compOp Mf ms)
sel false true  (just (j , tj)) f gs Mf ms = liftG f gs j Mf ms tj
sel false true  nothing         f gs Mf ms = nothing
sel false false _               f gs Mf ms = nothing

compTy-op-eq : ∀ f gs Mf tgs → compTy f gs (op Mf) tgs ≡
  sel (countHom tgs ==ℕ 0) (countHom tgs ==ℕ 1) (firstHom 0 tgs) f gs Mf (map baseM tgs)
compTy-op-eq f gs Mf tgs with countHom tgs ==ℕ 0 | countHom tgs ==ℕ 1 | firstHom 0 tgs
... | true  | _     | _             = refl
... | false | true  | just (j , tj) = refl
... | false | true  | nothing       = refl
... | false | false | _             = refl

------------------------------------------------------------------------
-- Substitution commutes with the list operations of the checker

module Ops (σ : Sub) where
  private φ = fo σ

  sFs-++ : ∀ xs ys → sFs φ (xs ++ ys) ≡ sFs φ xs ++ sFs φ ys
  sFs-++ []       ys = refl
  sFs-++ (x ∷ xs) ys = cong (sF φ x ∷_) (sFs-++ xs ys)

  out-sM : ∀ ms → map out (map (sM φ) ms) ≡ sFs φ (map out ms)
  out-sM []             = refl
  out-sM ((_ ▸ _) ∷ ms) = cong (_ ∷_) (out-sM ms)

  concatIns-sM : ∀ ms → concatIns (map (sM φ) ms) ≡ sFs φ (concatIns ms)
  concatIns-sM []              = refl
  concatIns-sM ((xs ▸ _) ∷ ms) =
    trans (cong (sFs φ xs ++_) (concatIns-sM ms)) (sym (sFs-++ xs (concatIns ms)))

  length-sFs : ∀ xs → length (sFs φ xs) ≡ length xs
  length-sFs []       = refl
  length-sFs (x ∷ xs) = cong suc (length-sFs xs)

  length-sTs : ∀ xs → length (sTs σ xs) ≡ length xs
  length-sTs []       = refl
  length-sTs (x ∷ xs) = cong suc (length-sTs xs)

  take-sM : ∀ n ms → take n (map (sM φ) ms) ≡ map (sM φ) (take n ms)
  take-sM zero    ms       = refl
  take-sM (suc n) []       = refl
  take-sM (suc n) (m ∷ ms) = cong (sM φ m ∷_) (take-sM n ms)

  length-++′ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
  length-++′ []       ys = refl
  length-++′ (x ∷ xs) ys = cong suc (length-++′ xs ys)

  sumIns-sM : ∀ ms → sumIns (map (sM φ) ms) ≡ sumIns ms
  sumIns-sM ms = trans (cong length (concatIns-sM ms)) (length-sFs (concatIns ms))

  sumIns-take : ∀ n ms → sumIns (take n (map (sM φ) ms)) ≡ sumIns (take n ms)
  sumIns-take n ms = trans (cong sumIns (take-sM n ms)) (sumIns-sM (take n ms))

  setAt-sM : ∀ j M ms → setAt j (sM φ M) (map (sM φ) ms) ≡ map (sM φ) (setAt j M ms)
  setAt-sM j       M []       = refl
  setAt-sM zero    M (_ ∷ ms) = refl
  setAt-sM (suc j) M (m ∷ ms) = cong (sM φ m ∷_) (setAt-sM j M ms)

  setAt-sTs : ∀ j s gs → setAt j (sT σ s) (sTs σ gs) ≡ sTs σ (setAt j s gs)
  setAt-sTs j       s []       = refl
  setAt-sTs zero    s (_ ∷ gs) = refl
  setAt-sTs (suc j) s (g ∷ gs) = cong (sT σ g ∷_) (setAt-sTs j s gs)

  baseM-sY : ∀ A → baseM (sY σ A) ≡ sM φ (baseM A)
  baseM-sY (op M)          = refl
  baseM-sY (hom _ _ A _ _) = baseM-sY A

  baseMs-sY : ∀ As → map baseM (map (sY σ) As) ≡ map (sM φ) (map baseM As)
  baseMs-sY []       = refl
  baseMs-sY (A ∷ As) = cong₂ _∷_ (baseM-sY A) (baseMs-sY As)

  dim-sY : ∀ A → dim (sY σ A) ≡ dim A
  dim-sY (op _)          = refl
  dim-sY (hom _ _ A _ _) = cong suc (dim-sY A)

  isHom-sY : ∀ A → isHom (sY σ A) ≡ isHom A
  isHom-sY (op _)          = refl
  isHom-sY (hom _ _ _ _ _) = refl

  countHom-sY : ∀ As → countHom (map (sY σ) As) ≡ countHom As
  countHom-sY []       = refl
  countHom-sY (A ∷ As) rewrite isHom-sY A | countHom-sY As = refl

  firstHom-sY : ∀ i As → firstHom i (map (sY σ) As) ≡
    mapM (λ p → fst p , sY σ (snd p)) (firstHom i As)
  firstHom-sY i []       = refl
  firstHom-sY i (A ∷ As) rewrite isHom-sY A with isHom A
  ... | true  = refl
  ... | false = firstHom-sY (suc i) As

  -- equal before substitution, equal after
  eqFms-sF : ∀ xs ys → T (eqFms xs ys) → T (eqFms (sFs φ xs) (sFs φ ys))
  eqFms-sF xs ys p rewrite eqFms-sound xs ys p = eqFms-refl (sFs φ ys)

  eqTy-sY : ∀ A B → T (eqTy A B) → T (eqTy (sY σ A) (sY σ B))
  eqTy-sY A B p rewrite eqTy-sound A B p = eqTy-refl (sY σ B)

  eqTm-sT : ∀ s u → T (eqTm s u) → T (eqTm (sT σ s) (sT σ u))
  eqTm-sT s u p rewrite eqTm-sound s u p = eqTm-refl (sT σ u)

  ----------------------------------------------------------------------
  -- The rules of compTy and glueTop

  compOp-sM : ∀ M ms N → compOp M ms ≡ just N →
              compOp (sM φ M) (map (sM φ) ms) ≡ just (sM φ N)
  compOp-sM (ys ▸ z) ms N e with if-inv (eqFms ys (map out ms)) e
  ... | p , refl rewrite out-sM ms | T→≡ (eqFms-sF ys (map out ms) p)
                       | concatIns-sM ms = refl

  mapOp-sM : ∀ M ms A → mapM op (compOp M ms) ≡ just A →
             mapM op (compOp (sM φ M) (map (sM φ) ms)) ≡ just (sY σ A)
  mapOp-sM M ms A e with compOp M ms in eq
  mapOp-sM M ms .(op N) refl | just N rewrite compOp-sM M ms N eq = refl

  liftF-sY : ∀ gs ms U A → liftF gs ms U ≡ just A →
             liftF (sTs σ gs) (map (sM φ) ms) (sY σ U) ≡ just (sY σ A)
  liftF-sY gs ms (op M) A e = mapOp-sM M ms A e
  liftF-sY gs ms (hom m g U s t) A e with bind-inv (liftF gs ms U) e
  ... | U′ , e1 , refl rewrite liftF-sY gs ms U U′ e1 | sumIns-take g ms = refl

  liftG-sY : ∀ f gs j Mf ms U A → liftG f gs j Mf ms U ≡ just A →
             liftG (sT σ f) (sTs σ gs) j (sM φ Mf) (map (sM φ) ms) (sY σ U) ≡ just (sY σ A)
  liftG-sY f gs j Mf ms (op M) A e rewrite setAt-sM j M ms =
    mapOp-sM Mf (setAt j M ms) A e
  liftG-sY f gs j Mf ms (hom m g U s t) A e with bind-inv (liftG f gs j Mf ms U) e
  ... | U′ , e1 , refl
    rewrite liftG-sY f gs j Mf ms U U′ e1 | sumIns-take j ms
          | setAt-sTs j s gs | setAt-sTs j t gs = refl

  sel-sY : ∀ b1 b2 mh f gs Mf ms A → sel b1 b2 mh f gs Mf ms ≡ just A →
    sel b1 b2 (mapM (λ p → fst p , sY σ (snd p)) mh) (sT σ f) (sTs σ gs)
        (sM φ Mf) (map (sM φ) ms) ≡ just (sY σ A)
  sel-sY true  b2    mh               f gs Mf ms A e = mapOp-sM Mf ms A e
  sel-sY false true  (just (j , tj)) f gs Mf ms A e = liftG-sY f gs j Mf ms tj A e
  sel-sY false true  nothing         f gs Mf ms A ()
  sel-sY false false mh              f gs Mf ms A ()

  compTy-sY : ∀ f gs tf tgs A → compTy f gs tf tgs ≡ just A →
    compTy (sT σ f) (sTs σ gs) (sY σ tf) (map (sY σ) tgs) ≡ just (sY σ A)
  compTy-sY f gs (op Mf) tgs A e
    rewrite compTy-op-eq (sT σ f) (sTs σ gs) (sM φ Mf) (map (sY σ) tgs)
          | countHom-sY tgs | firstHom-sY 0 tgs | baseMs-sY tgs =
    sel-sY (countHom tgs ==ℕ 0) (countHom tgs ==ℕ 1) (firstHom 0 tgs)
           f gs Mf (map baseM tgs) A
           (trans (sym (compTy-op-eq f gs Mf tgs)) e)
  compTy-sY f gs (hom m g U s t) tgs A e with if-inv (countHom tgs ==ℕ 0) e
  ... | p , e1 rewrite countHom-sY tgs | T→≡ p | baseMs-sY tgs =
    liftF-sY gs (map baseM tgs) (hom m g U s t) A e1

  -- a successful glue matches strictly below the top
  data _<_ : Nat → Nat → Set where
    z<s : ∀ {n} → zero < suc n
    s<s : ∀ {m n} → m < n → suc m < suc n

  <-suc : ∀ {m n} → m < n → m < suc n
  <-suc z<s     = z<s
  <-suc (s<s p) = s<s (<-suc p)

  n<sn : ∀ n → n < suc n
  n<sn zero    = z<s
  n<sn (suc n) = s<s (n<sn n)

  <-irr : ∀ {n} → n < n → ⊥
  <-irr (s<s p) = <-irr p

  glueTy-dim : ∀ am ap Tc qm qp pm pp X A →
    glueTy am ap Tc qm qp pm pp X ≡ just A → dim Tc < dim X
  glueTy-dim am ap Tc qm qp pm pp (op _) A ()
  glueTy-dim am ap Tc qm qp pm pp (hom m g U s t) A e
    with eqTy U Tc ∧ eqTm s qm ∧ eqTm t qp in b
  ... | true  = subst (λ k → k < suc (dim U))
                  (cong dim (eqTy-sound U Tc (∧-fst (≡→T b)))) (n<sn (dim U))
  ... | false with bind-inv (glueTy am ap Tc qm qp pm pp U) e
  ... | U′ , e1 , _ = <-suc (glueTy-dim am ap Tc qm qp pm pp U U′ e1)

  glueTy-sY : ∀ am ap Tc qm qp pm pp X A →
    glueTy am ap Tc qm qp pm pp X ≡ just A →
    glueTy (sT σ am) (sT σ ap) (sY σ Tc) (sT σ qm) (sT σ qp) (sT σ pm) (sT σ pp) (sY σ X)
      ≡ just (sY σ A)
  glueTy-sY am ap Tc qm qp pm pp (op _) A ()
  glueTy-sY am ap Tc qm qp pm pp (hom m g U s t) A e
    with eqTy U Tc ∧ eqTm s qm ∧ eqTm t qp in b
  ... | true with e
  ... | refl =
    let p  = ≡→T b
        p1 = ∧-fst p
        p2 = ∧-snd {eqTy U Tc} p
        p3 = ∧-fst p2
        p4 = ∧-snd {eqTm s qm} p2
    in subst (λ c → (if c then just (hom m g (sY σ Tc) (sT σ pm) (sT σ pp))
                        else (glueTy (sT σ am) (sT σ ap) (sY σ Tc) (sT σ qm) (sT σ qp)
                                (sT σ pm) (sT σ pp) (sY σ U) >>= λ U′ →
                              just (hom m g U′ (glue (sT σ am) (sT σ s) (sT σ ap))
                                               (glue (sT σ am) (sT σ t) (sT σ ap)))))
                       ≡ just (hom m g (sY σ Tc) (sT σ pm) (sT σ pp)))
             (sym (T→≡ (∧-intro (eqTy-sY U Tc p1) (∧-intro (eqTm-sT s qm p3) (eqTm-sT t qp p4)))))
             refl
  glueTy-sY am ap Tc qm qp pm pp (hom m g U s t) A e | false
    with bind-inv (glueTy am ap Tc qm qp pm pp U) e
  ... | U′ , e1 , refl
    rewrite eqTy-false (sY σ U) (sY σ Tc)
              (λ d → <-irr (subst (λ k → dim Tc < k)
                               (trans (sym (dim-sY U)) (trans d (dim-sY Tc)))
                               (glueTy-dim am ap Tc qm qp pm pp U U′ e1)))
          | glueTy-sY am ap Tc qm qp pm pp U U′ e1 = refl

  nrefl : ∀ n → (n ==ℕ n) ≡ true
  nrefl n = T→≡ (==ℕ-refl n)

  glueTop-sY : ∀ am ap ta tb tx A → glueTop am ap ta tb tx ≡ just A →
    glueTop (sT σ am) (sT σ ap) (sY σ ta) (sY σ tb) (sY σ tx) ≡ just (sY σ A)
  glueTop-sY am ap (hom inv g Tc pm qm) (hom inv g′ Tc′ pp qp) tx A e
    with if-inv ((g ==ℕ g′) ∧ eqTy Tc Tc′) e
  ... | p , e1 rewrite ==ℕ-sound g g′ (∧-fst p)
                     | eqTy-sound Tc Tc′ (∧-snd {g ==ℕ g′} p)
                     | nrefl g′
                     | T→≡ (eqTy-refl (sY σ Tc′)) =
    glueTy-sY am ap Tc′ qm qp pm pp tx A e1
  glueTop-sY am ap (op _)              _                       tx A ()
  glueTop-sY am ap (hom dir _ _ _ _)   _                       tx A ()
  glueTop-sY am ap (hom inv _ _ _ _)   (op _)                  tx A ()
  glueTop-sY am ap (hom inv _ _ _ _)   (hom dir _ _ _ _)       tx A ()

------------------------------------------------------------------------
-- The substitution lemma

if-true′ : ∀ {b} {A : Set} {x y : A} → T b → (if b then x else y) ≡ x
if-true′ {true} _ = refl

module _ {Γ Δ : Ctx} {σ : Sub} (h : Γ ⊢ σ ∶ Δ) where
  open Ops σ

  mutual
    sub-infer : ∀ x A → infer Δ x ≡ just A → infer Γ (sT σ x) ≡ just (sY σ A)
    sub-infer (var i)  A e    = app h i A e
    sub-infer (mP U V) _ refl = refl
    sub-infer (eL A C) _ refl = refl
    sub-infer (eR A C) _ refl = refl
    sub-infer (pP Δ Θ) _ refl = refl
    sub-infer pt       _ refl = refl
    sub-infer (iP _)   _ refl = refl
    sub-infer (idt A)  _ refl = refl
    sub-infer (comp f gs) A e with comp-inv Δ f gs e
    ... | tf , tgs , e1 , e2 , e3
      rewrite sub-infer f tf e1 | sub-inferL gs tgs e2 =
      compTy-sY f gs tf tgs A e3
    sub-infer (glue am x ap) A e with glue-inv Δ am x ap e
    ... | ta , tb , tx , e1 , e2 , e3 , e4
      rewrite sub-infer am ta e1 | sub-infer ap tb e2 | sub-infer x tx e3 =
      glueTop-sY am ap ta tb tx A e4
    sub-infer (here t e φs ts) A eq = sub-here t e φs ts A eq

    sub-here : ∀ t e φs ts A → infer Δ (here t e φs ts) ≡ just A →
               infer Γ (sT σ (here t e φs ts)) ≡ just (sY σ A)
    sub-here t e φs ts A eq
      with if-inv (okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t)
                     ∧ argsOk Δ (instS φs ts) ts (ctx t)) eq
    ... | p , refl =
      trans (if-true′ {okT t ∧ (length (sFs (fo σ) φs) ==ℕ nObj t)
                         ∧ (length (sTs σ ts) ==ℕ nCtx t)
                         ∧ argsOk Γ (instS (sFs (fo σ) φs) (sTs σ ts)) (sTs σ ts) (ctx t)}
               (∧-intro okt (∧-intro lφ′ (∧-intro lt″
                  (sub-args ts (ctx t) ctx-sc′ (∧-snd {length ts ==ℕ nCtx t} p3))))))
            (cong just (sym (inst-sY φs ts σ (goal t e) goal-sc′)))
      where
      okt = ∧-fst p
      p2  = ∧-snd {okT t} p
      p3  = ∧-snd {length φs ==ℕ nObj t} p2
      lφ : length φs ≡ nObj t
      lφ = ==ℕ-sound _ _ (∧-fst p2)
      lt′ : length ts ≡ nCtx t
      lt′ = ==ℕ-sound _ _ (∧-fst p3)
      lφ′ : T (length (sFs (fo σ) φs) ==ℕ nObj t)
      lφ′ = subst (λ q → T (q ==ℕ nObj t)) (sym (length-sFs φs)) (∧-fst p2)
      lt″ : T (length (sTs σ ts) ==ℕ nCtx t)
      lt″ = subst (λ q → T (q ==ℕ nCtx t)) (sym (length-sTs ts)) (∧-fst p3)
      open TmplScope t okt using (ctx-sc; goal-sc)
      sc≡ : ∀ B → T (scY (nObj t) (nCtx t) B) → T (scY (length φs) (length ts) B)
      sc≡ B q rewrite lφ | lt′ = q
      mapAll : ∀ Ψ → All (λ B → T (scY (nObj t) (nCtx t) B)) Ψ →
               All (λ B → T (scY (length φs) (length ts) B)) Ψ
      mapAll []      []       = []
      mapAll (B ∷ Ψ) (q ∷ qs) = sc≡ B q ∷ mapAll Ψ qs
      ctx-sc′ = mapAll (ctx t) ctx-sc
      goal-sc′ = sc≡ (goal t e) (goal-sc e)

    -- the instance's arguments stay well typed
    sub-args : ∀ {φs us} xs Ψ → All (λ B → T (scY (length φs) (length us) B)) Ψ →
               T (argsOk Δ (instS φs us) xs Ψ) →
               T (argsOk Γ (instS (sFs (fo σ) φs) (sTs σ us)) (sTs σ xs) Ψ)
    sub-args []       []      _        _ = tt
    sub-args {φs} {us} (x ∷ xs) (B ∷ Ψ) (q ∷ qs) p =
      ∧-intro (side (∧-fst p))
              (sub-args xs Ψ qs (∧-snd {eqMaybeTy (infer Δ x) (sY (instS φs us) B)} p))
      where
      side : T (eqMaybeTy (infer Δ x) (sY (instS φs us) B)) →
             T (eqMaybeTy (infer Γ (sT σ x)) (sY (instS (sFs (fo σ) φs) (sTs σ us)) B))
      side px with infer Δ x in ex
      ... | just C rewrite sub-infer x C ex
                         | sym (inst-sY φs us σ B q) = eqTy-sY C (sY (instS φs us) B) px
    sub-args []       (_ ∷ _) _ ()
    sub-args (_ ∷ _)  []      _ ()

    sub-inferL : ∀ xs As → inferL Δ xs ≡ just As →
                 inferL Γ (sTs σ xs) ≡ just (map (sY σ) As)
    sub-inferL []       _ refl = refl
    sub-inferL (x ∷ xs) As e with cons-inv Δ x xs e
    ... | A , Bs , e1 , e2 , refl
      rewrite sub-infer x A e1 | sub-inferL xs Bs e2 = refl

    sub-wf : ∀ A → T (wf Δ A) → T (wf Γ (sY σ A))
    sub-wf (op _) _ = tt
    sub-wf (hom m g A s t) p =
      let pA = ∧-fst p
          q  = ∧-snd {wf Δ A} p
          ps = ∧-fst q
          pt′ = ∧-snd {eqMaybeTy (infer Δ s) A} q
      in ∧-intro (sub-wf A pA) (∧-intro (side s ps) (side t pt′))
      where
        side : ∀ u → T (eqMaybeTy (infer Δ u) A) → T (eqMaybeTy (infer Γ (sT σ u)) (sY σ A))
        side u pu with infer Δ u in eu
        ... | just B rewrite sub-infer u B eu = eqTy-sY B A pu
