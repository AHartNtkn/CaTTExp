------------------------------------------------------------------------
-- The Gray model of P (ledger S3a, notes/uniform-checker.md §1.8 Route
-- step 1).
--
-- A term is read as its Gray table (GrayTab): 0-boundary, the supports
-- of its faces at every level, and its top support, where a generator
-- of the pasting diagram is the one-letter tuple of its name. This is
-- a model of FreeP's judgments on any generator list whose faces are
-- globular in this reading (`GenCheck.okGen`). So by FreeP's soundness,
-- two typed terms with different Gray tables are distinct cells of P.
--
-- The model is checked symbolically, once per operation boundary and
-- per equation schema (`okOp`, `okSchema`), as in FreeP0. A schema
-- variable x of dimension d is read as the table of letters
-- (S0 x, T0 x, Sd l x, Td l x, Top x) (`varTab`). Its guards give
-- equalities of the variables' objects (decided by connectivity, as in
-- FreeP0) and of supports. A support equality whose one side is a
-- single letter becomes a rewrite of that letter (`rules`); rewriting
-- is sound because it is itself an interpretation (SuppAlg.Rewrite).
-- The two sides must then agree level by level as sets of words. The
-- reading commutes with interpreting the letters (GrayTab.ev-hom), so
-- the check covers every instance. All operations and schemas of P
-- through degree four pass (`opsP-ok`, `eqsP-ok`, by computation).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.SuppAlg
open import CaTTExp.Uniform.SigP
open import CaTTExp.Uniform.FreeP
open import CaTTExp.Uniform.FreeP0 using (_≟Str_; Sym; S0; T0; Eqs; check; check-sound; Hold)
open import CaTTExp.Uniform.GrayTab
open import CaTTExp.Uniform.Arith using (_≟N_)
open import Agda.Builtin.String using (String; primStringEquality)

module CaTTExp.Uniform.FreeGray where

open Gen

------------------------------------------------------------------------
-- Small facts.

private
  eqN-sound : ∀ a b → T (a ==ℕ b) → a ≡ b
  eqN-sound zero    zero    _ = refl
  eqN-sound (suc a) (suc b) e = cong suc (eqN-sound a b e)

  eqN-refl : ∀ a → T (a ==ℕ a)
  eqN-refl zero    = tt
  eqN-refl (suc a) = eqN-refl a

  T≡ : ∀ {b} → T b → b ≡ true
  T≡ {true} _ = refl

  ≡T : ∀ {b} → b ≡ true → T b
  ≡T refl = tt

  rangeN : Nat → List Nat
  rangeN zero    = []
  rangeN (suc n) = n ∷ rangeN n

  lt-in : ∀ l n → T (l <ℕ n) → l ∈L rangeN n
  lt-in l zero    ()
  lt-in l (suc n) t with l ≟N n
  ... | yes refl = here
  ... | no ne    = there (lt-in l n (shrink l n t ne))
    where
    shrink : ∀ l n → T (l <ℕ suc n) → ¬ (l ≡ n) → T (l <ℕ n)
    shrink zero    zero    _ ne′ = ⊥-elim (ne′ refl)
    shrink zero    (suc n) _ _   = tt
    shrink (suc l) zero    () _
    shrink (suc l) (suc n) t′ ne′ = shrink l n t′ (λ e → ne′ (cong suc e))

  inR-lt : ∀ l n → T (inR l n) → T (l <ℕ n)
  inR-lt l n t = ∧-snd {0 <ℕ l} t

  -- Checking a property at every level 1 ≤ l < n.
  allLv : Nat → (Nat → Bool) → Bool
  allLv n ok = all (λ l → not (inR l n) ∨ ok l) (rangeN n)

  allLv-sound : ∀ n ok l → T (allLv n ok) → T (inR l n) → T (ok l)
  allLv-sound n ok l t r = go (rangeN n) t (lt-in l n (inR-lt l n r))
    where
    go : ∀ xs → T (all (λ l → not (inR l n) ∨ ok l) xs) → l ∈L xs → T (ok l)
    go (x ∷ xs) t′ here = imp (inR x n) (ok x) (∧-fst t′) r
      where imp : ∀ b c → T (not b ∨ c) → T b → T c
            imp true c u _ = u
    go (x ∷ xs) t′ (there m) = go xs (∧-snd {not (inR x n) ∨ ok x} t′) m

  ∈-all : ∀ {A : Set} (p : A → Bool) {x} xs → T (all p xs) → x ∈L xs → T (p x)
  ∈-all p (x ∷ xs) t here      = ∧-fst t
  ∈-all p (x ∷ xs) t (there m) = ∈-all p xs (∧-snd {p x} t) m

------------------------------------------------------------------------
-- Clean tables.

module _ {O K : Set} where
  Clean : Tab O K → Set
  Clean X = (∀ l → inR l (dm X) ≡ false → (s X l ≡ []) × (t X l ≡ [])) ×
            (dm X ≡ 0 → (top X ≡ []) × (hi X ≡ lo X))

  private
    if-false : ∀ {A : Set} {b} {x y : A} → b ≡ false → (if b then x else y) ≡ y
    if-false refl = refl
    if-true : ∀ {A : Set} {b} {x y : A} → b ≡ true → (if b then x else y) ≡ x
    if-true refl = refl
    zero-true : ∀ {n} → n ≡ 0 → (n ==ℕ 0) ≡ true
    zero-true refl = refl

  clean-apply : ∀ sh ins → Clean (apply {O} {K} sh ins)
  clean-apply sh ins = (λ l e → if-false e , if-false e) ,
                       (λ e → if-true (zero-true e) , if-true (zero-true e))

  clean-cmAll : ∀ o (X Y : Tab O K) → Clean (cmAll o X Y)
  clean-cmAll chiO  X Y = clean-apply (cmpSh chiO) (in4 (Eval.ev (env X Y) cmNone (fst (bounds chiO))) (Eval.ev (env X Y) cmNone (snd (bounds chiO))) X Y)
  clean-cmAll rO    X Y = clean-apply (cmpSh rO) (in4 (Eval.ev (env X Y) cmOnlyChi (fst (bounds rO))) (Eval.ev (env X Y) cmOnlyChi (snd (bounds rO))) X Y)
  clean-cmAll tO    X Y = clean-apply (cmpSh tO) (in4 (Eval.ev (env X Y) cmOnlyChi (fst (bounds tO))) (Eval.ev (env X Y) cmOnlyChi (snd (bounds tO))) X Y)
  clean-cmAll iotaO X Y = clean-apply (cmpSh iotaO) (in4 (Eval.ev (env X Y) cmOnlyChi (fst (bounds iotaO))) (Eval.ev (env X Y) cmOnlyChi (snd (bounds iotaO))) X Y)
  clean-cmAll hO    X Y = clean-apply (cmpSh hO) (in4 (Eval.ev (env X Y) cmOnlyChi (fst (bounds hO))) (Eval.ev (env X Y) cmOnlyChi (snd (bounds hO))) X Y)

  dm-cmAll : ∀ o (X Y : Tab O K) → dm (cmAll o X Y) ≡ cmpDim o
  dm-cmAll chiO  X Y = refl
  dm-cmAll rO    X Y = refl
  dm-cmAll tO    X Y = refl
  dm-cmAll iotaO X Y = refl
  dm-cmAll hO    X Y = refl

  -- Every table the reading produces is clean and has the term's
  -- dimension, given that the generators' tables are.
  module _ (gt : Nat → String → Tab O K)
           (gc-clean : ∀ d x → Clean (gt d x)) (gc-dm : ∀ d x → dm (gt d x) ≡ d) where
    private ev = Eval.ev gt cmAll

    clean-ev : ∀ u → Clean (ev u)
    clean-ev (v d x)       = gc-clean d x
    clean-ev (sF n x)      = clean-apply (faceSh false n) (in1 (ev x))
    clean-ev (tF n x)      = clean-apply (faceSh true n) (in1 (ev x))
    clean-ev (idT n x)     = clean-apply (idSh n) (in1 (ev x))
    clean-ev (comp n x y)  = clean-apply (compSh n) (in2 (ev x) (ev y))
    clean-ev (lft k n x y) = clean-apply (lftSh k n) (in2 (ev x) (ev y))
    clean-ev (rgt k n x y) = clean-apply (rgtSh k n) (in2 (ev x) (ev y))
    clean-ev (cmp o x y)   = clean-cmAll o (ev x) (ev y)

    dm-ev : ∀ u → dm (ev u) ≡ dim u
    dm-ev (v d x)       = gc-dm d x
    dm-ev (sF n x)      = refl
    dm-ev (tF n x)      = refl
    dm-ev (idT n x)     = refl
    dm-ev (comp n x y)  = refl
    dm-ev (lft k n x y) = refl
    dm-ev (rgt k n x y) = refl
    dm-ev (cmp o x y)   = dm-cmAll o (ev x) (ev y)

-- The reading commutes with substitution.
sub-ev : ∀ {O K} (gt : Nat → String → Tab O K) (σ : Sub) u →
         Eval.ev gt cmAll (sub σ u) ≡ Eval.ev (λ _ x → Eval.ev gt cmAll (σ x)) cmAll u
sub-ev gt σ (v d x)       = refl
sub-ev gt σ (sF n x)      = cong (λ X → apply (faceSh false n) (in1 X)) (sub-ev gt σ x)
sub-ev gt σ (tF n x)      = cong (λ X → apply (faceSh true n) (in1 X)) (sub-ev gt σ x)
sub-ev gt σ (idT n x)     = cong (λ X → apply (idSh n) (in1 X)) (sub-ev gt σ x)
sub-ev gt σ (comp n x y)  = cong₂ (λ X Y → apply (compSh n) (in2 X Y)) (sub-ev gt σ x) (sub-ev gt σ y)
sub-ev gt σ (lft k n x y) = cong₂ (λ X Y → apply (lftSh k n) (in2 X Y)) (sub-ev gt σ x) (sub-ev gt σ y)
sub-ev gt σ (rgt k n x y) = cong₂ (λ X Y → apply (rgtSh k n) (in2 X Y)) (sub-ev gt σ x) (sub-ev gt σ y)
sub-ev gt σ (cmp o x y)   = cong₂ (cmAll o) (sub-ev gt σ x) (sub-ev gt σ y)

------------------------------------------------------------------------
-- Symbolic letters and the table of a schema variable.

data GL : Set where
  Sd Td : Nat → String → GL
  Top   : String → GL

_≟GL_ : (a b : GL) → Dec (a ≡ b)
Sd l x ≟GL Sd m y with l ≟N m | x ≟Str y
... | yes refl | yes refl = yes refl
... | no ne    | _        = no λ { refl → ne refl }
... | yes _    | no ne    = no λ { refl → ne refl }
Td l x ≟GL Td m y with l ≟N m | x ≟Str y
... | yes refl | yes refl = yes refl
... | no ne    | _        = no λ { refl → ne refl }
... | yes _    | no ne    = no λ { refl → ne refl }
Top x ≟GL Top y with x ≟Str y
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }
Sd _ _ ≟GL Td _ _ = no λ ()
Sd _ _ ≟GL Top _  = no λ ()
Td _ _ ≟GL Sd _ _ = no λ ()
Td _ _ ≟GL Top _  = no λ ()
Top _  ≟GL Sd _ _ = no λ ()
Top _  ≟GL Td _ _ = no λ ()

letter : GL → SExp GL
letter k = (k ∷ []) ∷ []

varTab : Nat → String → Tab Sym GL
varTab d x = tab d (S0 x) (if d ==ℕ 0 then S0 x else T0 x)
                 (λ l → if inR l d then letter (Sd l x) else [])
                 (λ l → if inR l d then letter (Td l x) else [])
                 (if d ==ℕ 0 then [] else letter (Top x))

symEv : Tm → Tab Sym GL
symEv = Eval.ev varTab cmAll

------------------------------------------------------------------------
-- Rewrite rules from support equalities.

module RW = Rewrite _≟GL_

Rules : Set
Rules = List (GL × SExp GL)

applyR : Rules → SExp GL → SExp GL
applyR []             e = e
applyR ((k , e′) ∷ R) e = applyR R (RW.rw k e′ e)

single : SExp GL → Maybe GL
single ((k ∷ []) ∷ []) = just k
single _               = nothing

single-ok : ∀ e {k} → single e ≡ just k → e ≡ letter k
single-ok ((k ∷ []) ∷ []) refl = refl
single-ok []                      ()
single-ok ([] ∷ _)                ()
single-ok ((_ ∷ _ ∷ _) ∷ _)       ()
single-ok ((_ ∷ []) ∷ (_ ∷ _))    ()

occurs : GL → SExp GL → Bool
occurs k e = any (λ w → any (λ k′ → isYes (k ≟GL k′)) w) e
  where any : ∀ {A : Set} → (A → Bool) → List A → Bool
        any p []       = false
        any p (x ∷ xs) = p x ∨ any p xs

step : Rules → SExp GL × SExp GL → Rules
step R (a , b) = pick (single (applyR R a)) (single (applyR R b))
  where
  pick : Maybe GL → Maybe GL → Rules
  pick (just k) _        = if occurs k (applyR R b) then R else ((k , applyR R b) ∷ R)
  pick nothing  (just k) = if occurs k (applyR R a) then R else ((k , applyR R a) ∷ R)
  pick nothing  nothing  = R

pass : Rules → List (SExp GL × SExp GL) → Rules
pass R []       = R
pass R (f ∷ fs) = pass (step R f) fs

lengthF : List (SExp GL × SExp GL) → Nat
lengthF []       = 0
lengthF (_ ∷ xs) = suc (lengthF xs)

passes : List (SExp GL × SExp GL) → Nat → Rules → Rules
passes fs zero    R = R
passes fs (suc n) R = passes fs n (pass R fs)

rulesOf : List (SExp GL × SExp GL) → Rules
rulesOf fs = passes fs 2 []

module RuleSound {L : Set} (ρ : GL → SExp L) where
  open Interp ρ

  RulesOK : Rules → Set
  RulesOK R = ∀ {k e} → (k , e) ∈L R → iE e ≈S ρ k

  Facts : List (SExp GL × SExp GL) → Set
  Facts F = ∀ {a b} → (a , b) ∈L F → iE a ≈S iE b

  applyR-sound : ∀ R → RulesOK R → ∀ e → iE (applyR R e) ≈S iE e
  applyR-sound []             ok e = ≈S-refl
  applyR-sound ((k , e′) ∷ R) ok e =
    ≈S-trans (applyR-sound R (λ m → ok (there m)) (RW.rw k e′ e)) (RW.rewrite-sound ρ k e′ (ok here) e)

  private
    add : ∀ R k e → RulesOK R → iE e ≈S ρ k → RulesOK ((k , e) ∷ R)
    add R k e ok h here      = h
    add R k e ok h (there m) = ok m

    add? : ∀ b R k e → RulesOK R → iE e ≈S ρ k → RulesOK (if b then R else ((k , e) ∷ R))
    add? true  R k e ok h = ok
    add? false R k e ok h = add R k e ok h

  step-sound : ∀ R a b → RulesOK R → iE a ≈S iE b → RulesOK (step R (a , b))
  step-sound R a b ok h with single (applyR R a) in ea | single (applyR R b) in eb
  ... | just k | _ = add? (occurs k (applyR R b)) R k (applyR R b) ok
      (≈S-trans (applyR-sound R ok b)
       (≈S-trans (≈S-sym h)
        (≈S-trans (≈S-sym (applyR-sound R ok a))
         (≈S-trans (≡⇒≈S (cong iE (single-ok (applyR R a) ea))) (iE-letter k)))))
  ... | nothing | just k = add? (occurs k (applyR R a)) R k (applyR R a) ok
      (≈S-trans (applyR-sound R ok a)
       (≈S-trans h
        (≈S-trans (≈S-sym (applyR-sound R ok b))
         (≈S-trans (≡⇒≈S (cong iE (single-ok (applyR R b) eb))) (iE-letter k)))))
  ... | nothing | nothing = ok

  pass-sound : ∀ R F → RulesOK R → Facts F → RulesOK (pass R F)
  pass-sound R []            ok hf = ok
  pass-sound R ((a , b) ∷ F) ok hf =
    pass-sound (step R (a , b)) F (step-sound R a b ok (hf here)) (λ m → hf (there m))

  rulesOf-sound : ∀ F → Facts F → RulesOK (rulesOf F)
  rulesOf-sound F hf = go′ 2 [] (λ ())
    where
    go′ : ∀ n R → RulesOK R → RulesOK (passes F n R)
    go′ zero    R ok = ok
    go′ (suc n) R ok = go′ n (pass R F) (pass-sound R F ok hf)

------------------------------------------------------------------------
-- The check of one equation (or operation boundary).

guardTerms : List Guard → List Tm
guardTerms []             = []
guardTerms ((l , r) ∷ gs) = l ∷ r ∷ guardTerms gs

-- A leaf (d , x) is a declared variable of dimension d.
leafOK : List Tm → Nat × String → Bool
leafOK []       _       = false
leafOK (a ∷ as) (d , x) = (isYes (varName a ≟Str x) ∧ (dim a ==ℕ d)) ∨ leafOK as (d , x)

leavesOK : List Tm → List Tm → Bool
leavesOK as us = all (λ u → all (leafOK as) (leaves u)) us

objEqs : List Guard → Eqs
objEqs []             = []
objEqs ((l , r) ∷ gs) = (lo (symEv l) , lo (symEv r)) ∷ (hi (symEv l) , hi (symEv r)) ∷ objEqs gs

levelFacts : Tab Sym GL → Tab Sym GL → List Nat → List (SExp GL × SExp GL)
levelFacts L R []       = []
levelFacts L R (i ∷ is) = (s L i , s R i) ∷ (t L i , t R i) ∷ levelFacts L R is

suppFacts : List Guard → List (SExp GL × SExp GL)
suppFacts []             = []
suppFacts ((l , r) ∷ gs) =
  (top (symEv l) , top (symEv r)) ∷ levelFacts (symEv l) (symEv r) (rangeN (dm (symEv l))) ++ suppFacts gs

module _ (gs : List Guard) where
  private
    Rs : Rules
    Rs = rulesOf (suppFacts gs)
  sameS : SExp GL → SExp GL → Bool
  sameS a b = RW.same? (applyR Rs a) (applyR Rs b)

okEqG : List Tm → List Guard → Tm → Tm → Bool
okEqG as gs l r =
  leavesOK as (l ∷ r ∷ guardTerms gs) ∧ (dm L ==ℕ dm R) ∧
  check E (lo L) (lo R) ∧ check E (hi L) (hi R) ∧
  allLv (dm L) (λ i → sameS gs (s L i) (s R i) ∧ sameS gs (t L i) (t R i)) ∧
  sameS gs (top L) (top R)
  where
  L R : Tab Sym GL
  L = symEv l
  R = symEv r
  E : Eqs
  E = objEqs gs

------------------------------------------------------------------------
-- Soundness of the check, for any clean reading of the generators.

private
  ≡⇒≈T : ∀ {O K} {A B : Tab O K} → A ≡ B → A ≈T B
  ≡⇒≈T refl = ≈T-refl

  varTab-clean : ∀ d x → Clean (varTab d x)
  varTab-clean d x = (λ l e → if-f e , if-f e) , (λ e → if-t (zt e) , if-t (zt e))
    where
    if-f : ∀ {A : Set} {b} {p q : A} → b ≡ false → (if b then p else q) ≡ q
    if-f refl = refl
    if-t : ∀ {A : Set} {b} {p q : A} → b ≡ true → (if b then p else q) ≡ p
    if-t refl = refl
    zt : ∀ {n} → n ≡ 0 → (n ==ℕ 0) ≡ true
    zt refl = refl

module Sound (gt : Nat → String → Tab String String)
             (gc-clean : ∀ d x → Clean (gt d x)) (gc-dm : ∀ d x → dm (gt d x) ≡ d) where

  evG : Tm → Tab String String
  evG = Eval.ev gt cmAll

  module _ (σ : Sub) where
    ρo : Sym → String
    ρo (S0 x) = lo (evG (σ x))
    ρo (T0 x) = hi (evG (σ x))

    ρ : GL → SExp String
    ρ (Sd l x) = s (evG (σ x)) l
    ρ (Td l x) = t (evG (σ x)) l
    ρ (Top x)  = top (evG (σ x))

    open Hom ρo ρ
    open Interp ρ
    open RuleSound ρ

    private
      cl : ∀ u → Clean (evG u)
      cl = clean-ev gt gc-clean gc-dm
      dmE : ∀ u → dm (evG u) ≡ dim u
      dmE = dm-ev gt gc-clean gc-dm

    var-ok : ∀ d x → dim (σ x) ≡ d → mapT (varTab d x) ≈T evG (σ x)
    var-ok d x e =
      sym dmX , refl , hiOK (d ==ℕ 0) refl , lvl Sd s (λ _ → refl) (λ l e → fst (fst (cl (σ x)) l e)) ,
      lvl Td t (λ _ → refl) (λ l e → snd (fst (cl (σ x)) l e)) , topOK (d ==ℕ 0) refl
      where
      X = evG (σ x)
      dmX : dm X ≡ d
      dmX = trans (dmE (σ x)) e
      hiOK : ∀ b → (d ==ℕ 0) ≡ b → ρo (if b then S0 x else T0 x) ≡ hi X
      hiOK true  z = sym (snd (snd (cl (σ x)) (trans dmX (eqN-sound d 0 (≡T z)))))
      hiOK false z = refl
      topOK : ∀ b → (d ==ℕ 0) ≡ b → iE (if b then [] else letter (Top x)) ≈S top X
      topOK true  z = ≡⇒≈S (sym (fst (snd (cl (σ x)) (trans dmX (eqN-sound d 0 (≡T z))))))
      topOK false z = iE-letter (Top x)
      lvl : (Mk : Nat → String → GL) (side : Tab String String → Nat → SExp String) →
            (∀ l → ρ (Mk l x) ≡ side X l) →
            (∀ l → inR l (dm X) ≡ false → side X l ≡ []) →
            ∀ l → iE (if inR l d then letter (Mk l x) else []) ≈S side X l
      lvl Mk side ρok clean l with inR l d in r
      ... | true  = ≈S-trans (iE-letter (Mk l x)) (≡⇒≈S (ρok l))
      ... | false = ≡⇒≈S (sym (clean l (trans (cong (inR l) dmX) r)))

    Leaves : Tm → Set
    Leaves u = ∀ {d x} → (d , x) ∈L leaves u → dim (σ x) ≡ d

    main : ∀ u → Leaves u → evG (sub σ u) ≈T mapT (symEv u)
    main u h =
      ≈T-trans (≡⇒≈T (sub-ev gt σ u))
        (≈T-sym (ev-hom {varTab} {λ _ x → evG (σ x)} {cmAll} {cmAll} cmAll-hom cmAll-cong u
                  (λ m → var-ok _ _ (h m))))

    Dims : List Tm → Set
    Dims as = ∀ {a} → a ∈L as → dim (σ (varName a)) ≡ dim a

    leafOK-sound : ∀ as {d x} → Dims as → T (leafOK as (d , x)) → dim (σ x) ≡ d
    leafOK-sound (a ∷ as) {d} {x} h t with varName a ≟Str x | dim a ==ℕ d in e
    ... | yes refl | true  = trans (h here) (eqN-sound (dim a) d (≡T e))
    ... | yes refl | false = leafOK-sound as (λ m → h (there m)) t
    ... | no _     | _     = leafOK-sound as (λ m → h (there m)) t

    leaves-sound : ∀ as us → Dims as → T (leavesOK as us) → ∀ {u} → u ∈L us → Leaves u
    leaves-sound as us h t {u} m lm =
      leafOK-sound as h (∈-all (leafOK as) (leaves u) (∈-all (λ u′ → all (leafOK as) (leaves u′)) us t m) lm)

    GuardsC : List Guard → Set
    GuardsC gs = ∀ {g} → g ∈L gs → evG (sub σ (fst g)) ≈T evG (sub σ (snd g))

    SymG : List Guard → Set
    SymG gs = ∀ {l r} → (l , r) ∈L gs → mapT (symEv l) ≈T mapT (symEv r)

    private
      guard-in : ∀ gs {l r} → (l , r) ∈L gs → (l ∈L guardTerms gs) × (r ∈L guardTerms gs)
      guard-in ((l , r) ∷ gs) here      = here , there here
      guard-in ((l′ , r′) ∷ gs) (there m) =
        there (there (fst (guard-in gs m))) , there (there (snd (guard-in gs m)))

      obj-hold : ∀ gs → SymG gs → Hold ρo (objEqs gs)
      obj-hold ((l , r) ∷ gs) h here              = fst (snd (h here))
      obj-hold ((l , r) ∷ gs) h (there here)      = fst (snd (snd (h here)))
      obj-hold ((l , r) ∷ gs) h (there (there m)) = obj-hold gs (λ k → h (there k)) m

      level-facts : ∀ L R is → (∀ i → iE (s L i) ≈S iE (s R i)) → (∀ i → iE (t L i) ≈S iE (t R i)) →
                    Facts (levelFacts L R is)
      level-facts L R (i ∷ is) hs ht here              = hs i
      level-facts L R (i ∷ is) hs ht (there here)      = ht i
      level-facts L R (i ∷ is) hs ht (there (there m)) = level-facts L R is hs ht m

      supp-facts : ∀ gs → SymG gs → Facts (suppFacts gs)
      supp-facts ((l , r) ∷ gs) h here = snd (snd (snd (snd (snd (h here)))))
      supp-facts ((l , r) ∷ gs) h (there m)
        with ∈-++⁻ (levelFacts (symEv l) (symEv r) (rangeN (dm (symEv l)))) m
      ... | inj₁ m′ = level-facts (symEv l) (symEv r) _
                        (fst (snd (snd (snd (h here))))) (fst (snd (snd (snd (snd (h here)))))) m′
      ... | inj₂ m′ = supp-facts gs (λ k → h (there k)) m′

      symClean : ∀ u → Clean (symEv u)
      symClean = clean-ev varTab varTab-clean (λ _ _ → refl)

      sameS-sound : ∀ gs → SymG gs → ∀ a b → T (sameS gs a b) → iE a ≈S iE b
      sameS-sound gs h a b t =
        ≈S-trans (≈S-sym (applyR-sound Rs ok a))
          (≈S-trans (iE-cong (RW.same-sound (applyR Rs a) (applyR Rs b) t)) (applyR-sound Rs ok b))
        where
        Rs = rulesOf (suppFacts gs)
        ok = rulesOf-sound (suppFacts gs) (supp-facts gs h)

    by-check : ∀ as gs l r → T (okEqG as gs l r) → Dims as → GuardsC gs → evG (sub σ l) ≈T evG (sub σ r)
    by-check as gs l r tt′ hd hg =
      ≈T-trans (main l (lv (here)))
        (≈T-trans mid (≈T-sym (main r (lv (there here)))))
      where
      L = symEv l
      R = symEv r
      E = objEqs gs
      t1 = ∧-fst tt′
      r1 = ∧-snd {leavesOK as (l ∷ r ∷ guardTerms gs)} tt′
      t2 = ∧-fst r1
      r2 = ∧-snd {dm L ==ℕ dm R} r1
      t3 = ∧-fst r2
      r3 = ∧-snd {check E (lo L) (lo R)} r2
      t4 = ∧-fst r3
      r4 = ∧-snd {check E (hi L) (hi R)} r3
      t5 = ∧-fst r4
      t6 = ∧-snd {allLv (dm L) (λ i → sameS gs (s L i) (s R i) ∧ sameS gs (t L i) (t R i))} r4
      lv : ∀ {u} → u ∈L (l ∷ r ∷ guardTerms gs) → Leaves u
      lv = leaves-sound as (l ∷ r ∷ guardTerms gs) hd t1
      symG : SymG gs
      symG {gl} {gr} m =
        ≈T-trans (≈T-sym (main gl (lv (there (there (fst (guard-in gs m)))))))
          (≈T-trans (hg m) (main gr (lv (there (there (snd (guard-in gs m)))))))
      dmLR : dm L ≡ dm R
      dmLR = eqN-sound (dm L) (dm R) t2
      level : (side : Tab Sym GL → Nat → SExp GL) →
              (∀ i → inR i (dm L) ≡ false → (side L i ≡ []) × (side R i ≡ [])) →
              (∀ i → T (inR i (dm L)) → T (sameS gs (side L i) (side R i))) →
              ∀ i → iE (side L i) ≈S iE (side R i)
      level side cln ok i with inR i (dm L) in e
      ... | true  = sameS-sound gs symG (side L i) (side R i) (ok i (≡T e))
      ... | false = ≡⇒≈S (cong iE (trans (fst (cln i e)) (sym (snd (cln i e)))))
      lvOK : ∀ i → T (inR i (dm L)) → T (sameS gs (s L i) (s R i) ∧ sameS gs (t L i) (t R i))
      lvOK i r′ = allLv-sound (dm L) (λ j → sameS gs (s L j) (s R j) ∧ sameS gs (t L j) (t R j)) i t5 r′
      cleanS : ∀ i → inR i (dm L) ≡ false → (s L i ≡ []) × (s R i ≡ [])
      cleanS i e = fst (fst (symClean l) i e) , fst (fst (symClean r) i (trans (cong (inR i) (sym dmLR)) e))
      cleanT : ∀ i → inR i (dm L) ≡ false → (t L i ≡ []) × (t R i ≡ [])
      cleanT i e = snd (fst (symClean l) i e) , snd (fst (symClean r) i (trans (cong (inR i) (sym dmLR)) e))
      mid : mapT L ≈T mapT R
      mid = dmLR ,
            check-sound ρo E {lo L} {lo R} t3 (obj-hold gs symG) ,
            check-sound ρo E {hi L} {hi R} t4 (obj-hold gs symG) ,
            level s cleanS (λ i r′ → ∧-fst (lvOK i r′)) ,
            level t cleanT (λ i r′ → ∧-snd {sameS gs (s L i) (s R i)} (lvOK i r′)) ,
            sameS-sound gs symG (top L) (top R) t6

------------------------------------------------------------------------
-- The checks, one per operation and per schema.

module _ (o : OpSpec) where
  private
    as = OpSpec.args o
    gs = OpSpec.guardsO o
    ap = OpSpec.applied o
  okSrcG okTgtG okArgsG : Bool
  okSrcG  = okEqG as gs (sF (dim ap) ap) (OpSpec.srcO o)
  okTgtG  = okEqG as gs (tF (dim ap) ap) (OpSpec.tgtO o)
  okArgsG = leavesOK as (ap ∷ [])

okOp : OpSpec → Bool
okOp o = okSrcG o ∧ okTgtG o ∧ okArgsG o

okSchema : Schema → Bool
okSchema e = okEqG (Schema.vars e) (Schema.guards e) (Schema.lhs e) (Schema.rhs e)

------------------------------------------------------------------------
-- The generators' tables. A generator g of dimension n + 1 has top
-- support {(g)}; its levels below n are those of its source (for s)
-- and target (for t), and its n-level is {(gsrc g)} and {(gtgt g)}.

lookupG : List Gen → String → Maybe Gen
lookupG []       x = nothing
lookupG (g ∷ gs) x = if primStringEquality (gname g) x then just g else lookupG gs x

mutual
  genTab : List Gen → Nat → String → Tab String String
  genTab gs zero    x = tab 0 x x (λ _ → []) (λ _ → []) []
  genTab gs (suc n) x = genStep gs n x (lookupG gs x)

  genStep : List Gen → Nat → String → Maybe Gen → Tab String String
  genStep gs n x nothing  = tab (suc n) x x (λ _ → []) (λ _ → []) ((x ∷ []) ∷ [])
  genStep gs n x (just g) =
    tab (suc n) (lo (genTab gs n (gsrc g))) (hi (genTab gs n (gtgt g)))
        (λ l → if inR l (suc n) then (if l ==ℕ n then (gsrc g ∷ []) ∷ [] else s (genTab gs n (gsrc g)) l) else [])
        (λ l → if inR l (suc n) then (if l ==ℕ n then (gtgt g ∷ []) ∷ [] else t (genTab gs n (gtgt g)) l) else [])
        ((x ∷ []) ∷ [])

private
  if-f : ∀ {A : Set} {b} {p q : A} → b ≡ false → (if b then p else q) ≡ q
  if-f refl = refl

genTab-clean : ∀ gs d x → Clean (genTab gs d x)
genTab-clean gs zero    x = (λ _ _ → refl , refl) , (λ _ → refl , refl)
genTab-clean gs (suc n) x = gstep (lookupG gs x)
  where
  gstep : ∀ m → Clean (genStep gs n x m)
  gstep nothing  = (λ _ _ → refl , refl) , (λ ())
  gstep (just g) = (λ l e → if-f e , if-f e) , (λ ())

genTab-dm : ∀ gs d x → dm (genTab gs d x) ≡ d
genTab-dm gs zero    x = refl
genTab-dm gs (suc n) x = gstep (lookupG gs x)
  where
  gstep : ∀ m → dm (genStep gs n x m) ≡ suc n
  gstep nothing  = refl
  gstep (just g) = refl

-- Decided equality of clean concrete tables.
module RS = Rewrite _≟Str_

tabEq? : Tab String String → Tab String String → Bool
tabEq? X Y = (dm X ==ℕ dm Y) ∧ isYes (lo X ≟Str lo Y) ∧ isYes (hi X ≟Str hi Y) ∧
             allLv (dm X) (λ i → RS.same? (s X i) (s Y i) ∧ RS.same? (t X i) (t Y i)) ∧
             RS.same? (top X) (top Y)

tabEq-sound : ∀ X Y → Clean X → Clean Y → T (tabEq? X Y) → X ≈T Y
tabEq-sound X Y cX cY t0 =
  dXY , isYes-sound (lo X ≟Str lo Y) t2 , isYes-sound (hi X ≟Str hi Y) t3 ,
  level s (λ i e → fst (fst cX i e) , fst (fst cY i (trans (cong (inR i) (sym dXY)) e))) (λ i r → ∧-fst (lv i r)) ,
  level t (λ i e → snd (fst cX i e) , snd (fst cY i (trans (cong (inR i) (sym dXY)) e)))
          (λ i r → ∧-snd {RS.same? (s X i) (s Y i)} (lv i r)) ,
  RS.same-sound (top X) (top Y) t5
  where
  t1 = ∧-fst t0
  r1 = ∧-snd {dm X ==ℕ dm Y} t0
  t2 = ∧-fst r1
  r2 = ∧-snd {isYes (lo X ≟Str lo Y)} r1
  t3 = ∧-fst r2
  r3 = ∧-snd {isYes (hi X ≟Str hi Y)} r2
  t4 = ∧-fst r3
  t5 = ∧-snd {allLv (dm X) (λ i → RS.same? (s X i) (s Y i) ∧ RS.same? (t X i) (t Y i))} r3
  dXY = eqN-sound (dm X) (dm Y) t1
  lv : ∀ i → T (inR i (dm X)) → T (RS.same? (s X i) (s Y i) ∧ RS.same? (t X i) (t Y i))
  lv i r = allLv-sound (dm X) (λ j → RS.same? (s X j) (s Y j) ∧ RS.same? (t X j) (t Y j)) i t4 r
  level : (side : Tab String String → Nat → SExp String) →
          (∀ i → inR i (dm X) ≡ false → (side X i ≡ []) × (side Y i ≡ [])) →
          (∀ i → T (inR i (dm X)) → T (RS.same? (side X i) (side Y i))) →
          ∀ i → side X i ≈S side Y i
  level side cln ok i with inR i (dm X) in e
  ... | true  = RS.same-sound (side X i) (side Y i) (ok i (≡T e))
  ... | false = ≡⇒≈S (trans (fst (cln i e)) (sym (snd (cln i e))))

module GenCheck (gens : List Gen) where
  evGen : Tm → Tab String String
  evGen = Eval.ev (genTab gens) cmAll

  okGenD : Gen → Nat → Bool
  okGenD g zero    = true
  okGenD g (suc n) =
    tabEq? (evGen (sF (suc n) (v (suc n) (gname g)))) (evGen (v n (gsrc g))) ∧
    tabEq? (evGen (tF (suc n) (v (suc n) (gname g)))) (evGen (v n (gtgt g)))

  okGen : Gen → Bool
  okGen g = okGenD g (gdim g)

------------------------------------------------------------------------
-- The model.

private
  leafOK-mem : ∀ as {d x} → T (leafOK as (d , x)) → Σ Tm λ a → (a ∈L as) × (varName a ≡ x)
  leafOK-mem (a ∷ as) {d} {x} t with varName a ≟Str x | dim a ==ℕ d
  ... | yes e | true  = a , here , e
  ... | yes _ | false with leafOK-mem as t
  ...   | b , m , e = b , there m , e
  leafOK-mem (a ∷ as) {d} {x} t | no _ | _ with leafOK-mem as t
  ...   | b , m , e = b , there m , e

module ModelG (ops : List OpSpec) (eqs : List Schema) (gens : List Gen)
              (ops-ok  : T (all okOp ops))
              (eqs-ok  : T (all okSchema eqs))
              (gens-ok : T (all (GenCheck.okGen gens) gens)) where
  open Models ops eqs gens
  open Sound (genTab gens) (genTab-clean gens) (genTab-dm gens)

  private
    cl : ∀ u → Clean (evG u)
    cl = clean-ev (genTab gens) (genTab-clean gens) (genTab-dm gens)

    gen-at : ∀ {g n} → g ∈L gens → gdim g ≡ suc n → T (GenCheck.okGenD gens g (suc n))
    gen-at {g} m e = subst (λ d → T (GenCheck.okGenD gens g d)) e (∈-all (GenCheck.okGen gens) gens gens-ok m)

    op-ok : ∀ {o} → o ∈L ops → T (okOp o)
    op-ok = ∈-all okOp ops ops-ok

  model : Model
  model = record
    { M        = Tab String String
    ; _≈_      = _≈T_
    ; ≈-refl   = ≈T-refl
    ; ≈-sym    = ≈T-sym
    ; ≈-trans  = ≈T-trans
    ; ev       = λ u → just (evG u)
    ; def-gen  = λ _ → tt
    ; def-s    = λ _ _ → tt
    ; def-t    = λ _ _ → tt
    ; def-op   = λ _ _ _ _ → tt
    ; cong-s   = λ {n} e → apply-cong (faceSh false n) (in1-cong e)
    ; cong-t   = λ {n} e → apply-cong (faceSh true n) (in1-cong e)
    ; cong-op  = λ {o} {σ} {τ} m pw →
        let ap = OpSpec.applied o
            t  = ∧-snd {okTgtG o} (∧-snd {okSrcG o} (op-ok m))
        in ≈T-trans (≡⇒≈T (sub-ev (genTab gens) σ ap))
             (≈T-trans (ev-cong {gen = λ _ x → evG (σ x)} {gen′ = λ _ x → evG (τ x)} {cm = cmAll} cmAll-cong ap
                          (λ {d} {x} lm → leaf-pw o σ τ pw (∈-all (leafOK (OpSpec.args o)) (leaves ap) (∧-fst t) lm)))
                (≡⇒≈T (sym (sub-ev (genTab gens) τ ap))))
    ; sat-eq   = λ {e} {σ} m ha hg →
        by-check σ (Schema.vars e) (Schema.guards e) (Schema.lhs e) (Schema.rhs e)
          (∈-all okSchema eqs eqs-ok m) (λ k → snd (ha k)) hg
    ; sat-src  = λ {o} {σ} m _ ha hg →
        by-check σ (OpSpec.args o) (OpSpec.guardsO o) (sF (dim (OpSpec.applied o)) (OpSpec.applied o)) (OpSpec.srcO o)
          (∧-fst (op-ok m)) (λ k → snd (ha k)) hg
    ; sat-tgt  = λ {o} {σ} m _ ha hg →
        by-check σ (OpSpec.args o) (OpSpec.guardsO o) (tF (dim (OpSpec.applied o)) (OpSpec.applied o)) (OpSpec.tgtO o)
          (∧-fst (∧-snd {okSrcG o} (op-ok m))) (λ k → snd (ha k)) hg
    ; sat-gsrc = λ {g} {n} m e →
        subst (λ d → evG (sF (suc n) (v d (gname g))) ≈T evG (v n (gsrc g))) (sym e)
          (tabEq-sound _ _ (cl (sF (suc n) (v (suc n) (gname g)))) (cl (v n (gsrc g))) (∧-fst (gen-at m e)))
    ; sat-gtgt = λ {g} {n} m e →
        subst (λ d → evG (tF (suc n) (v d (gname g))) ≈T evG (v n (gtgt g))) (sym e)
          (tabEq-sound _ _ (cl (tF (suc n) (v (suc n) (gname g)))) (cl (v n (gtgt g)))
             (∧-snd {tabEq? (evG (sF (suc n) (v (suc n) (gname g)))) (evG (v n (gsrc g)))} (gen-at m e)))
    }
    where
    leaf-pw : ∀ o σ τ → (∀ {a} → a ∈L OpSpec.args o → evG (σ (varName a)) ≈T evG (τ (varName a))) →
              ∀ {d x} → T (leafOK (OpSpec.args o) (d , x)) → evG (σ x) ≈T evG (τ x)
    leaf-pw o σ τ pw t with leafOK-mem (OpSpec.args o) t
    ... | a , m , refl = pw m

  open Soundness model public

------------------------------------------------------------------------
-- P passes every check (about a minute of normalization).

opsP-ok : T (all okOp opsP)
opsP-ok = tt

eqsP-ok : T (all okSchema (equationsUpTo 4))
eqsP-ok = tt

-- The check is not vacuous: χ with its arguments swapped is refused.
χ-swap : okSchema (schema "swap" (v 2 "x" ∷ v 2 "y" ∷ [])
                     ((tF 1 (tF 2 (v 2 "x")) , sF 1 (sF 2 (v 2 "y"))) ∷ [])
                     (cmp chiO (v 2 "x") (v 2 "y")) (cmp chiO (v 2 "y") (v 2 "x"))) ≡ false
χ-swap = refl

------------------------------------------------------------------------
-- A separation FreeP0 cannot make. On
--
--     a --f, f′--> b --g, g′--> c,   α : f ⇒ f′,  β : g ⇒ g′
--
-- the two whiskered composites (α g)(f′ β) and (f β)(α g′) have the
-- same 0-boundary, but different Gray tops {(α,g),(f′,β)} and
-- {(f,β),(α,g′)}. So they are distinct cells of P: interchange along
-- an object is not forced.

module ExampleG where
  gs : List Gen
  gs = gen "a" 0 "" "" ∷ gen "b" 0 "" "" ∷ gen "c" 0 "" "" ∷
       gen "f" 1 "a" "b" ∷ gen "f'" 1 "a" "b" ∷ gen "g" 1 "b" "c" ∷ gen "g'" 1 "b" "c" ∷
       gen "alpha" 2 "f" "f'" ∷ gen "beta" 2 "g" "g'" ∷ []

  open ModelG opsP (equationsUpTo 4) gs opsP-ok eqsP-ok tt
  open FreeP gs

  α β f f′ g g′ : Tm
  α = v 2 "alpha" ; β = v 2 "beta"
  f = v 1 "f" ; f′ = v 1 "f'" ; g = v 1 "g" ; g′ = v 1 "g'"

  left right : Tm
  left  = comp 2 (rgt 1 2 α g) (lft 1 2 f′ β)
  right = comp 2 (lft 1 2 f β) (rgt 1 2 α g′)

  -- Both are typed, so this is a statement about cells.
  private
    σ2 : Tm → Tm → Sub
    σ2 A B nm = if primStringEquality nm "x0" then A else B

    gf′ : gen "f'" 1 "a" "b" ∈L gs
    gf′ = there (there (there (there (here))))
    gg : gen "g" 1 "b" "c" ∈L gs
    gg = there (there (there (there (there (here)))))
    gα : gen "alpha" 2 "f" "f'" ∈L gs
    gα = there (there (there (there (there (there (there (here)))))))
    gβ : gen "beta" 2 "g" "g'" ∈L gs
    gβ = there (there (there (there (there (there (there (there (here))))))))

    tα : Typed (tF 2 α)
    tα = t-t (t-gen gα) refl
    sβ : Typed (sF 2 β)
    sβ = t-s (t-gen gβ) refl

    -- t₁ f′ = b = s₁ g = s₁ (s₂ β) = t₁ (t₂ α)
    b≐ : sF 1 g ≐ tF 1 f′
    b≐ = ≐-trans (≐-gsrc gg refl) (≐-sym (≐-gtgt gf′ refl))
    tα≐ : tF 1 (tF 2 α) ≐ sF 1 g
    tα≐ = ≐-trans (≐-t (≐-gtgt gα refl)) (≐-sym b≐)
    sβ≐ : tF 1 f′ ≐ sF 1 (sF 2 β)
    sβ≐ = ≐-trans (≐-sym b≐) (≐-s (≐-sym (≐-gsrc gβ refl)))

    args11 : ∀ {A B} → Typed A → dim A ≡ 1 → Typed B → dim B ≡ 1 → ArgsOK (σ2 A B) (v 1 "x0" ∷ v 1 "x1" ∷ [])
    args11 ta da tb db here         = ta , da
    args11 ta da tb db (there here) = tb , db

    args21 : ∀ {A B} → Typed A → dim A ≡ 2 → Typed B → dim B ≡ 1 → ArgsOK (σ2 A B) (v 2 "x0" ∷ v 1 "x1" ∷ [])
    args21 ta da tb db here         = ta , da
    args21 ta da tb db (there here) = tb , db

    args12 : ∀ {A B} → Typed A → dim A ≡ 1 → Typed B → dim B ≡ 2 → ArgsOK (σ2 A B) (v 1 "x0" ∷ v 2 "x1" ∷ [])
    args12 ta da tb db here         = ta , da
    args12 ta da tb db (there here) = tb , db

    args22 : ∀ {A B} → Typed A → dim A ≡ 2 → Typed B → dim B ≡ 2 → ArgsOK (σ2 A B) (v 2 "x0" ∷ v 2 "x1" ∷ [])
    args22 ta da tb db here         = ta , da
    args22 ta da tb db (there here) = tb , db

    αg-args = args21 (t-gen gα) refl (t-gen gg) refl
    αg-guards : GuardsOK (σ2 α g) ((tF 1 (tF 2 (v 2 "x0")) , sF 1 (v 1 "x1")) ∷ [])
    αg-guards here = tα≐
    f′β-args = args12 (t-gen gf′) refl (t-gen gβ) refl
    f′β-guards : GuardsOK (σ2 f′ β) ((tF 1 (v 1 "x0") , sF 1 (sF 2 (v 2 "x1"))) ∷ [])
    f′β-guards here = sβ≐

    αg : Typed (rgt 1 2 α g)
    αg = t-op {σ = σ2 α g} (there (there (there (there (there here))))) refl αg-args αg-guards
    f′β : Typed (lft 1 2 f′ β)
    f′β = t-op {σ = σ2 f′ β} (there (there (there (there here)))) refl f′β-args f′β-guards

    -- t₂ (α g) = (t₂ α) g = f′ (s₂ β) = s₂ (f′ β)
    mid≐ : tF 2 (rgt 1 2 α g) ≐ sF 2 (lft 1 2 f′ β)
    mid≐ =
      ≐-trans (≐-tgt {σ = σ2 α g} (there (there (there (there (there here))))) refl αg-args αg-guards)
        (≐-trans (≐-op {σ = σ2 (tF 2 α) g} {τ = σ2 f′ (sF 2 β)} (there here) refl
                   (args11 tα refl (t-gen gg) refl) (λ { here → tα≐ })
                   (args11 (t-gen gf′) refl sβ refl) (λ { here → sβ≐ })
                   (λ { here → ≐-gtgt gα refl ; (there here) → ≐-sym (≐-gsrc gβ refl) }))
          (≐-sym (≐-src {σ = σ2 f′ β} (there (there (there (there here)))) refl f′β-args f′β-guards)))

    gf : gen "f" 1 "a" "b" ∈L gs
    gf = there (there (there (here)))
    gg′ : gen "g'" 1 "b" "c" ∈L gs
    gg′ = there (there (there (there (there (there (here))))))

    sα : Typed (sF 2 α)
    sα = t-s (t-gen gα) refl
    tβ : Typed (tF 2 β)
    tβ = t-t (t-gen gβ) refl

    -- t₁ f = b = s₁ g′ = s₁ (t₂ β) = t₁ (s₂ α)
    b≐′ : sF 1 g′ ≐ tF 1 f
    b≐′ = ≐-trans (≐-gsrc gg′ refl) (≐-sym (≐-gtgt gf refl))
    fβ-guards : GuardsOK (σ2 f β) ((tF 1 (v 1 "x0") , sF 1 (sF 2 (v 2 "x1"))) ∷ [])
    fβ-guards here = ≐-trans (≐-trans (≐-gtgt gf refl) (≐-sym (≐-gsrc gg refl))) (≐-s (≐-sym (≐-gsrc gβ refl)))
    αg′-guards : GuardsOK (σ2 α g′) ((tF 1 (tF 2 (v 2 "x0")) , sF 1 (v 1 "x1")) ∷ [])
    αg′-guards here = ≐-trans (≐-t (≐-gtgt gα refl)) (≐-trans (≐-gtgt gf′ refl) (≐-sym (≐-gsrc gg′ refl)))
    fβ-args = args12 (t-gen gf) refl (t-gen gβ) refl
    αg′-args = args21 (t-gen gα) refl (t-gen gg′) refl

    fβ : Typed (lft 1 2 f β)
    fβ = t-op {σ = σ2 f β} (there (there (there (there (here))))) refl fβ-args fβ-guards
    αg′ : Typed (rgt 1 2 α g′)
    αg′ = t-op {σ = σ2 α g′} (there (there (there (there (there (here)))))) refl αg′-args αg′-guards

    -- t₂ (f β) = f (t₂ β) = (s₂ α) g′ = s₂ (α g′)
    mid≐′ : tF 2 (lft 1 2 f β) ≐ sF 2 (rgt 1 2 α g′)
    mid≐′ =
      ≐-trans (≐-tgt {σ = σ2 f β} (there (there (there (there (here))))) refl fβ-args fβ-guards)
        (≐-trans (≐-op {σ = σ2 f (tF 2 β)} {τ = σ2 (sF 2 α) g′} (there (here)) refl
                   (args11 (t-gen gf) refl tβ refl)
                   (λ { here → ≐-trans (≐-sym b≐′) (≐-s (≐-sym (≐-gtgt gβ refl))) })
                   (args11 sα refl (t-gen gg′) refl)
                   (λ { here → ≐-trans (≐-t (≐-gsrc gα refl)) (≐-sym b≐′) })
                   (λ { here → ≐-sym (≐-gsrc gα refl) ; (there here) → ≐-gtgt gβ refl }))
          (≐-sym (≐-src {σ = σ2 α g′} (there (there (there (there (there (here)))))) refl αg′-args αg′-guards)))

  left-typed : Typed left
  left-typed = t-op {σ = σ2 (rgt 1 2 α g) (lft 1 2 f′ β)} (there (there (there here))) refl
                 (args22 αg refl f′β refl) (λ { here → mid≐ })

  right-typed : Typed right
  right-typed = t-op {σ = σ2 (lft 1 2 f β) (rgt 1 2 α g′)} (there (there (there (here)))) refl
                  (args22 fβ refl αg′ refl) (λ { here → mid≐′ })

  left≠right : ¬ (left ≐ right)
  left≠right = separate λ e → notIn (fst (snd (snd (snd (snd (snd e))))) here)
    where
    notIn : ¬ (("alpha" ∷ "g" ∷ []) ∈L top (Sound.evG (genTab gs) (genTab-clean gs) (genTab-dm gs) right))
    notIn (there (there ()))
