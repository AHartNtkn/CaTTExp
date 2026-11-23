------------------------------------------------------------------------
-- A consistency witness for FreeP: the model of 0-boundaries
-- (ledger S3a; review of #436, point 1).
--
-- Every cell of P has a 0-source and a 0-target, and every equation and
-- boundary of P relates cells with the same 0-boundary. Reading a term
-- as the pair (0-source, 0-target) of names of 0-cells gives a model
-- of FreeP's judgments, on any generator list whose faces are globular
-- at dimension 0 (`GenCheck.okGen`). By FreeP's soundness, two typed terms with
-- different 0-boundaries are distinct cells. In particular FreeP does
-- not identify distinct 0-cells (`Example0.a≠c`).
--
-- The model is checked symbolically. `loS t` and `hiS t` name the
-- variable face that gives t's 0-source and 0-target. Each schema and
-- each operation boundary is checked once, by computation: its two sides
-- have the same symbolic 0-boundary, up to the equalities between
-- variable faces that its guards impose, and that its 0-dimensional
-- variables impose (a 0-cell is its own 0-source and 0-target,
-- `zero-dim`); equality is connectivity in a small graph (`check`).
-- Substitution commutes with the symbolic reading (`lo-sub`, `hi-sub`),
-- so the check covers every instance. All operations and schemas of P
-- through degree four pass (`opsP-ok`, `eqsP-ok`, by computation).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Arith using (_≟N_)
open import CaTTExp.Uniform.Grid using (≟List)
open import Agda.Builtin.String using (String; primStringToList; primStringEquality)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.String.Properties using (primStringToListInjective)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import CaTTExp.Uniform.SigP
open import CaTTExp.Uniform.FreeP
import CaTTExp.Uniform.FiniteGraph as FG

module CaTTExp.Uniform.FreeP0 where

open Gen

------------------------------------------------------------------------
-- Decidable equality of strings.

_≟Ch_ : (a b : Char) → Dec (a ≡ b)
a ≟Ch b with primCharToNat a ≟N primCharToNat b
... | yes e = yes (primCharToNatInjective a b e)
... | no ne = no λ e → ne (cong primCharToNat e)

_≟Str_ : (a b : String) → Dec (a ≡ b)
a ≟Str b with ≟List _≟Ch_ (primStringToList a) (primStringToList b)
... | yes e = yes (primStringToListInjective a b e)
... | no ne = no λ e → ne (cong primStringToList e)

------------------------------------------------------------------------
-- Symbolic 0-boundaries.

data Sym : Set where
  S0 T0 : String → Sym

_≟Sym_ : (a b : Sym) → Dec (a ≡ b)
S0 x ≟Sym S0 y with x ≟Str y
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }
T0 x ≟Sym T0 y with x ≟Str y
... | yes refl = yes refl
... | no ne    = no λ { refl → ne refl }
S0 _ ≟Sym T0 _ = no λ ()
T0 _ ≟Sym S0 _ = no λ ()

symName : Sym → String
symName (S0 x) = x
symName (T0 x) = x

isIota : CmpOp → Bool
isIota iotaO = true
isIota _     = false

mutual
  loS : Tm → Sym
  loS (v _ x)       = S0 x
  loS (sF n x)      = loS x
  loS (tF n x)      = if n <ℕ 2 then hiS x else loS x
  loS (idT _ x)     = loS x
  loS (comp _ x y)  = loS x
  loS (lft _ _ u f) = loS u
  loS (rgt _ _ f u) = loS f
  loS (cmp o x y)   = loS x

  hiS : Tm → Sym
  hiS (v _ x)       = T0 x
  hiS (sF n x)      = if n <ℕ 2 then loS x else hiS x
  hiS (tF n x)      = hiS x
  hiS (idT _ x)     = hiS x
  hiS (comp n x y)  = if n ==ℕ 0 then loS x else hiS y
  hiS (lft _ n u f) = if n ==ℕ 0 then loS u else hiS f
  hiS (rgt _ n f u) = if n ==ℕ 0 then loS f else hiS u
  hiS (cmp o x y)   = if isIota o then hiS x else hiS y

------------------------------------------------------------------------
-- Concrete 0-boundaries, given the 0-boundary of each variable.

module Values (ρl ρh : String → String) where
  mutual
    lo : Tm → String
    lo (v _ x)       = ρl x
    lo (sF n x)      = lo x
    lo (tF n x)      = if n <ℕ 2 then hi x else lo x
    lo (idT _ x)     = lo x
    lo (comp _ x y)  = lo x
    lo (lft _ _ u f) = lo u
    lo (rgt _ _ f u) = lo f
    lo (cmp o x y)   = lo x

    hi : Tm → String
    hi (v d x)       = if d ==ℕ 0 then ρl x else ρh x
    hi (sF n x)      = if n <ℕ 2 then lo x else hi x
    hi (tF n x)      = hi x
    hi (idT _ x)     = hi x
    hi (comp n x y)  = if n ==ℕ 0 then lo x else hi y
    hi (lft _ n u f) = if n ==ℕ 0 then lo u else hi f
    hi (rgt _ n f u) = if n ==ℕ 0 then lo f else hi u
    hi (cmp o x y)   = if isIota o then hi x else hi y

  -- A cell of dimension 0 is its own 0-source and 0-target.
  zero-dim : ∀ t → dim t ≡ 0 → lo t ≡ hi t
  zero-dim (v zero x) e = refl
  zero-dim (sF zero x) e = refl
  zero-dim (sF (suc zero) x) e = refl
  zero-dim (tF zero x) e = refl
  zero-dim (tF (suc zero) x) e = refl
  zero-dim (comp zero x y) e = refl
  zero-dim (lft k zero u f) e = refl
  zero-dim (rgt k zero f u) e = refl
  zero-dim (cmp chiO x y) ()
  zero-dim (cmp rO x y) ()
  zero-dim (cmp tO x y) ()
  zero-dim (cmp iotaO x y) ()
  zero-dim (cmp hO x y) ()

  -- Substitution commutes with the symbolic reading.
  module _ (σ : Sub) where
    interp : Sym → String
    interp (S0 x) = lo (σ x)
    interp (T0 x) = hi (σ x)

    mutual
      lo-sub : ∀ t → lo (sub σ t) ≡ interp (loS t)
      lo-sub (v _ x)       = refl
      lo-sub (sF n x)      = lo-sub x
      lo-sub (tF n x) with n <ℕ 2
      ... | true  = hi-sub x
      ... | false = lo-sub x
      lo-sub (idT _ x)     = lo-sub x
      lo-sub (comp _ x y)  = lo-sub x
      lo-sub (lft _ _ u f) = lo-sub u
      lo-sub (rgt _ _ f u) = lo-sub f
      lo-sub (cmp o x y)   = lo-sub x

      hi-sub : ∀ t → hi (sub σ t) ≡ interp (hiS t)
      hi-sub (v _ x)       = refl
      hi-sub (sF n x) with n <ℕ 2
      ... | true  = lo-sub x
      ... | false = hi-sub x
      hi-sub (tF n x)      = hi-sub x
      hi-sub (idT _ x)     = hi-sub x
      hi-sub (comp n x y) with n ==ℕ 0
      ... | true  = lo-sub x
      ... | false = hi-sub y
      hi-sub (lft _ n u f) with n ==ℕ 0
      ... | true  = lo-sub u
      ... | false = hi-sub f
      hi-sub (rgt _ n f u) with n ==ℕ 0
      ... | true  = lo-sub f
      ... | false = hi-sub u
      hi-sub (cmp o x y) with isIota o
      ... | true  = hi-sub x
      ... | false = hi-sub y

------------------------------------------------------------------------
-- Equality of symbols up to a list of equations: connectivity.

Eqs : Set
Eqs = List (Sym × Sym)

private
  add : ∀ {a s : Sym} → Dec (a ≡ s) → Sym → List Sym → List Sym
  add (yes _) z zs = z ∷ zs
  add (no _)  z zs = zs

nbE : Eqs → Sym → List Sym
nbE []             s = []
nbE ((a , b) ∷ E) s = add (a ≟Sym s) b (add (b ≟Sym s) a (nbE E s))

Hold : (Sym → String) → Eqs → Set
Hold I E = ∀ {a b} → (a , b) ∈L E → I a ≡ I b

private
  len : ∀ {A : Set} → List A → Nat
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

  nb-sound : ∀ I E {x y} → y ∈L nbE E x → Hold I E → I x ≡ I y
  nb-sound I ((a , b) ∷ E) {x} m h with a ≟Sym x | b ≟Sym x
  nb-sound I ((a , b) ∷ E) here h | yes refl | _ = h here
  nb-sound I ((a , b) ∷ E) (there here) h | yes refl | yes refl = sym (h here)
  nb-sound I ((a , b) ∷ E) (there (there m)) h | yes refl | yes refl = nb-sound I E m (λ k → h (there k))
  nb-sound I ((a , b) ∷ E) (there m) h | yes refl | no _ = nb-sound I E m (λ k → h (there k))
  nb-sound I ((a , b) ∷ E) here h | no _ | yes refl = sym (h here)
  nb-sound I ((a , b) ∷ E) (there m) h | no _ | yes refl = nb-sound I E m (λ k → h (there k))
  nb-sound I ((a , b) ∷ E) m h | no _ | no _ = nb-sound I E m (λ k → h (there k))

check : Eqs → Sym → Sym → Bool
check E x z = isYes (FG.within? _≟Sym_ (nbE E) (suc (len E + len E)) x z)

check-sound : ∀ I E {x z} → T (check E x z) → Hold I E → I x ≡ I z
check-sound I E {x} {z} t h = go (isYes-sound (FG.within? _≟Sym_ (nbE E) _ x z) t)
  where
  go : ∀ {k x z} → FG.Within _≟Sym_ (nbE E) k x z → I x ≡ I z
  go FG.now         = refl
  go (FG.later m w) = trans (nb-sound I E m h) (go w)

------------------------------------------------------------------------
-- The checks, one per schema and per operation boundary.

guardEqs : List Guard → Eqs
guardEqs []             = []
guardEqs ((l , r) ∷ gs) = (loS l , loS r) ∷ (hiS l , hiS r) ∷ guardEqs gs

-- A variable of dimension 0 has equal 0-source and 0-target.
zeroEqs : List Tm → Eqs
zeroEqs []       = []
zeroEqs (a ∷ as) = if dim a ==ℕ 0 then (S0 (varName a) , T0 (varName a)) ∷ zeroEqs as else zeroEqs as

allEqs : List Tm → List Guard → Eqs
allEqs as gs = zeroEqs as ++ guardEqs gs

okEq : List Tm → List Guard → Tm → Tm → Bool
okEq as gs l r = check (allEqs as gs) (loS l) (loS r) ∧ check (allEqs as gs) (hiS l) (hiS r)

private
  memS : String → List String → Bool
  memS x []       = false
  memS x (y ∷ ys) = isYes (x ≟Str y) ∨ memS x ys

module _ (o : OpSpec) where
  private
    as = OpSpec.args o
    gs = OpSpec.guardsO o
    ap = OpSpec.applied o
    names = mapK varName (OpSpec.args o)
  okSrc okTgt okLo okHi : Bool
  okSrc = okEq as gs (sF (dim ap) ap) (OpSpec.srcO o)
  okTgt = okEq as gs (tF (dim ap) ap) (OpSpec.tgtO o)
  okLo  = memS (symName (loS ap)) names
  okHi  = memS (symName (hiS ap)) names

okOp : OpSpec → Bool
okOp o = okSrc o ∧ okTgt o ∧ okLo o ∧ okHi o

okSchema : Schema → Bool
okSchema e = okEq (Schema.vars e) (Schema.guards e) (Schema.lhs e) (Schema.rhs e)

-- Generators: 0-boundaries given by ρl, ρh, matching their faces.
module GenCheck (ρl ρh : String → String) where
  open Values ρl ρh
  module _ (g : Gen) (n : Nat) where
    gv : Tm
    gv = v (suc n) (gname g)
    g1 g2 g3 g4 : Bool
    g1 = isYes (lo (sF (suc n) gv) ≟Str lo (v n (gsrc g)))
    g2 = isYes (hi (sF (suc n) gv) ≟Str hi (v n (gsrc g)))
    g3 = isYes (lo (tF (suc n) gv) ≟Str lo (v n (gtgt g)))
    g4 = isYes (hi (tF (suc n) gv) ≟Str hi (v n (gtgt g)))

  okGenD : Gen → Nat → Bool
  okGenD g zero    = true
  okGenD g (suc n) = g1 g n ∧ g2 g n ∧ g3 g n ∧ g4 g n

  okGen : Gen → Bool
  okGen g = okGenD g (gdim g)

------------------------------------------------------------------------
-- The model.

private
  ∈-all : ∀ {A : Set} (p : A → Bool) {x} xs → T (all p xs) → x ∈L xs → T (p x)
  ∈-all p (x ∷ xs) t here      = ∧-fst t
  ∈-all p (x ∷ xs) t (there m) = ∈-all p xs (∧-snd {p x} t) m

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  eqN-sound : ∀ a b → (a ==ℕ b) ≡ true → a ≡ b
  eqN-sound zero    zero    e = refl
  eqN-sound (suc a) (suc b) e = cong suc (eqN-sound a b e)

  ,-inj : ∀ {A B : Set} {a a′ : A} {b b′ : B} → (a , b) ≡ (a′ , b′) → (a ≡ a′) × (b ≡ b′)
  ,-inj refl = refl , refl

  memS-sound : ∀ x ys → T (memS x ys) → Σ String λ y → (y ∈L ys) × (x ≡ y)
  memS-sound x (y ∷ ys) t with x ≟Str y
  ... | yes e = y , here , e
  ... | no _ with memS-sound x ys t
  ...   | z , m , e = z , there m , e

module Model0 (ops : List OpSpec) (eqs : List Schema) (gens : List Gen)
              (ρl ρh : String → String)
              (ops-ok  : T (all okOp ops))
              (eqs-ok  : T (all okSchema eqs))
              (gens-ok : T (all (GenCheck.okGen ρl ρh) gens)) where
  open Values ρl ρh
  open Models ops eqs gens

  ev : Tm → Maybe (String × String)
  ev t = just (lo t , hi t)

  private
    ev-sub : ∀ σ t → ev (sub σ t) ≡ just (interp σ (loS t) , interp σ (hiS t))
    ev-sub σ t = cong₂ (λ a b → just (a , b)) (lo-sub σ t) (hi-sub σ t)

    guards-hold : ∀ σ gs → (∀ {g} → g ∈L gs → ev (sub σ (fst g)) ≡ ev (sub σ (snd g))) →
                  Hold (interp σ) (guardEqs gs)
    guards-hold σ ((l , r) ∷ gs) h here =
      trans (sym (lo-sub σ l)) (trans (fst (,-inj (just-inj (h here)))) (lo-sub σ r))
    guards-hold σ ((l , r) ∷ gs) h (there here) =
      trans (sym (hi-sub σ l)) (trans (snd (,-inj (just-inj (h here)))) (hi-sub σ r))
    guards-hold σ ((l , r) ∷ gs) h (there (there m)) = guards-hold σ gs (λ k → h (there k)) m

    zero-hold : ∀ σ as → (∀ {a} → a ∈L as → dim (σ (varName a)) ≡ dim a) →
                Hold (interp σ) (zeroEqs as)
    zero-hold σ (a ∷ as) h m with dim a ==ℕ 0 in e
    zero-hold σ (a ∷ as) h here      | true =
      zero-dim (σ (varName a)) (trans (h here) (eqN-sound (dim a) 0 e))
    zero-hold σ (a ∷ as) h (there m) | true  = zero-hold σ as (λ k → h (there k)) m
    zero-hold σ (a ∷ as) h m         | false = zero-hold σ as (λ k → h (there k)) m

    all-hold : ∀ σ as gs → (∀ {a} → a ∈L as → dim (σ (varName a)) ≡ dim a) →
               (∀ {g} → g ∈L gs → ev (sub σ (fst g)) ≡ ev (sub σ (snd g))) →
               Hold (interp σ) (allEqs as gs)
    all-hold σ as gs hd hg m with ∈-++⁻ (zeroEqs as) m
    ... | inj₁ m′ = zero-hold σ as hd m′
    ... | inj₂ m′ = guards-hold σ gs hg m′

    by-check : ∀ σ as gs l r → T (okEq as gs l r) →
               (∀ {a} → a ∈L as → dim (σ (varName a)) ≡ dim a) →
               (∀ {g} → g ∈L gs → ev (sub σ (fst g)) ≡ ev (sub σ (snd g))) →
               ev (sub σ l) ≡ ev (sub σ r)
    by-check σ as gs l r t hd h =
      trans (ev-sub σ l)
        (trans (cong₂ (λ a b → just (a , b))
                  (check-sound (interp σ) (allEqs as gs) {loS l} {loS r}
                     (∧-fst {check (allEqs as gs) (loS l) (loS r)} t) (all-hold σ as gs hd h))
                  (check-sound (interp σ) (allEqs as gs) {hiS l} {hiS r}
                     (∧-snd {check (allEqs as gs) (loS l) (loS r)} t)
                     (all-hold σ as gs hd h)))
               (sym (ev-sub σ r)))

    -- An operation's value depends only on its declared arguments.
    from-args : ∀ {o} σ τ s → T (memS (symName s) (mapK varName (OpSpec.args o))) →
                (∀ {a} → a ∈L OpSpec.args o → ev (σ (varName a)) ≡ ev (τ (varName a))) →
                interp σ s ≡ interp τ s
    from-args {o} σ τ (S0 x) t pw with memS-sound x _ t
    ... | y , m , refl with ∈-map⁻ varName (OpSpec.args o) m
    ...   | a , ma , refl = fst (,-inj (just-inj (pw ma)))
    from-args {o} σ τ (T0 x) t pw with memS-sound x _ t
    ... | y , m , refl with ∈-map⁻ varName (OpSpec.args o) m
    ...   | a , ma , refl = snd (,-inj (just-inj (pw ma)))

    gen-ok : ∀ {g} → g ∈L gens → T (GenCheck.okGen ρl ρh g)
    gen-ok = ∈-all _ gens gens-ok

    yes-≡ : ∀ {a b : String} → T (isYes (a ≟Str b)) → a ≡ b
    yes-≡ {a} {b} t = isYes-sound (a ≟Str b) t

  model : Model
  model = record
    { M  = String × String
    ; ev = ev
    ; def-gen  = λ _ → tt
    ; def-s    = λ _ _ → tt
    ; def-t    = λ _ _ → tt
    ; def-op   = λ _ _ _ _ → tt
    ; cong-s   = λ {n} e → cong (λ p → just (fst p , (if n <ℕ 2 then fst p else snd p))) (just-inj e)
    ; cong-t   = λ {n} e → cong (λ p → just ((if n <ℕ 2 then snd p else fst p) , snd p)) (just-inj e)
    ; cong-op  = λ {o} {σ} {τ} m pw →
        let t = ∈-all okOp ops ops-ok m
            ap = OpSpec.applied o
            t₃ = ∧-snd {okTgt o} (∧-snd {okSrc o} t)
        in trans (ev-sub σ ap)
             (trans (cong₂ (λ a b → just (a , b))
                       (from-args {o} σ τ (loS ap) (∧-fst t₃) pw)
                       (from-args {o} σ τ (hiS ap) (∧-snd {okLo o} t₃) pw))
                    (sym (ev-sub τ ap)))
    ; sat-eq   = λ {e} {σ} m ha hg →
        by-check σ (Schema.vars e) (Schema.guards e) (Schema.lhs e) (Schema.rhs e)
          (∈-all okSchema eqs eqs-ok m) (λ k → snd (ha k)) hg
    ; sat-src  = λ {o} {σ} m _ ha hg →
        let ap = OpSpec.applied o in
        by-check σ (OpSpec.args o) (OpSpec.guardsO o) (sF (dim ap) ap) (OpSpec.srcO o)
          (∧-fst (∈-all okOp ops ops-ok m)) (λ k → snd (ha k)) hg
    ; sat-tgt  = λ {o} {σ} m _ ha hg →
        let ap = OpSpec.applied o in
        by-check σ (OpSpec.args o) (OpSpec.guardsO o) (tF (dim ap) ap) (OpSpec.tgtO o)
          (∧-fst (∧-snd {okSrc o} (∈-all okOp ops ops-ok m))) (λ k → snd (ha k)) hg
    ; sat-gsrc = gsrc-ok
    ; sat-gtgt = gtgt-ok
    }
    where
    gen-at : ∀ {g n} → g ∈L gens → gdim g ≡ suc n → T (GenCheck.okGenD ρl ρh g (suc n))
    gen-at {g} m e = subst (λ d → T (GenCheck.okGenD ρl ρh g d)) e (gen-ok m)

    gsrc-ok : ∀ {g n} → g ∈L gens → gdim g ≡ suc n →
           ev (sF (suc n) (v (gdim g) (gname g))) ≡ ev (v n (gsrc g))
    gsrc-ok {g} {n} m e rewrite e =
      let t = gen-at {g} {n} m e in
      cong₂ (λ a b → just (a , b)) (yes-≡ (∧-fst t)) (yes-≡ (∧-fst (∧-snd {GenCheck.g1 ρl ρh g n} t)))
    gtgt-ok : ∀ {g n} → g ∈L gens → gdim g ≡ suc n →
           ev (tF (suc n) (v (gdim g) (gname g))) ≡ ev (v n (gtgt g))
    gtgt-ok {g} {n} m e rewrite e =
      let t = ∧-snd {GenCheck.g2 ρl ρh g n} (∧-snd {GenCheck.g1 ρl ρh g n} (gen-at {g} {n} m e)) in
      cong₂ (λ a b → just (a , b)) (yes-≡ (∧-fst t)) (yes-≡ (∧-snd {GenCheck.g3 ρl ρh g n} t))

  open Soundness model public

------------------------------------------------------------------------
-- P passes every check.

opsP-ok : T (all okOp opsP)
opsP-ok = tt

eqsP-ok : T (all okSchema (equationsUpTo 4))
eqsP-ok = tt

------------------------------------------------------------------------
-- The consistency witness on a --f--> b --g--> c.

module Example0 where
  gs : List Gen
  gs = gen "a" 0 "" "" ∷ gen "b" 0 "" "" ∷ gen "c" 0 "" "" ∷
       gen "f" 1 "a" "b" ∷ gen "g" 1 "b" "c" ∷ []

  ρl ρh : String → String
  ρl x = if primStringEquality x "f" then "a" else if primStringEquality x "g" then "b" else x
  ρh x = if primStringEquality x "f" then "b" else if primStringEquality x "g" then "c" else x

  open Model0 opsP (equationsUpTo 4) gs ρl ρh opsP-ok eqsP-ok tt

  open FreeP gs using (_≐_)

  a≠c : ¬ (v 0 "a" ≐ v 0 "c")
  a≠c = separate λ ()

  f≠g : ¬ (v 1 "f" ≐ v 1 "g")
  f≠g = separate λ ()
