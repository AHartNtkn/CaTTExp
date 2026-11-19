------------------------------------------------------------------------
-- Naturality lifts of terms along a disk extension (ledger D15).
--
-- Setting: a context Γ, a set of "travelling" variables a (isDep), a
-- renaming b(−) sending each of them to its parallel copy, and for
-- each a a lift L(a): either a *derivative* L(a) : a → b(a) (when the
-- boundary of a does not travel), or a *square* (when it does)
--
--   o = true :  L(c) : L(∂⁻c) ; b(c)  →  c ; L(∂⁺c)
--   o = false:  L(c) : c ; L(∂⁺c)     →  L(∂⁻c) ; b(c)
--
-- `lift` extends L to terms built from coherences:
--
-- * every travelling argument a derivative: one coherence over the
--   pasting scheme with those arguments raised by one dimension
--   (a composite if the term's boundary does not travel, an invertible
--   coherence otherwise);
-- * a vertical chain of squares: pasting of the squares, with
--   regroupings (Elab.stepAt);
-- * a whiskering (rw, lw, whiskIn) of a single square: the whiskered
--   square between two functoriality coherences.
--
-- Squares whose own boundary lifts are squares, and squares as
-- arguments of any other coherence, are not handled (`err`). They do
-- not arise when lifting the vertical composites of VCompLift (checked
-- up to dimension 4); see notes/conjectures/vertical-composition-by-lifts.md.
--
-- Uncertified, like Elab: the certified checker re-checks the output.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Lift where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Natural using (rnTm)
open import CaTTExp.GrayCtx.Show using (_<>_)
open import Agda.Builtin.String using (String; primShowNat)

------------------------------------------------------------------------
-- Results with an error message.

data Res (A : Set) : Set where
  ok  : A → Res A
  err : String → Res A

infixl 1 _>>=ʳ_
_>>=ʳ_ : ∀ {A B : Set} → Res A → (A → Res B) → Res B
ok a  >>=ʳ f = f a
err s >>=ʳ f = err s

fromM : ∀ {A : Set} → String → Maybe A → Res A
fromM s (just a) = ok a
fromM s nothing  = err s

toM : ∀ {A : Set} → Res A → Maybe A
toM (ok a)  = just a
toM (err _) = nothing

guardʳ : String → Bool → Res ⊤
guardʳ s true  = ok tt
guardʳ s false = err s

------------------------------------------------------------------------
-- Lists.

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

anyL : ∀ {A : Set} → (A → Bool) → List A → Bool
anyL p []       = false
anyL p (x ∷ xs) = p x ∨ anyL p xs

lenL : ∀ {A : Set} → List A → Nat
lenL []       = 0
lenL (_ ∷ xs) = suc (lenL xs)

takeL dropL : ∀ {A : Set} → Nat → List A → List A
takeL zero    xs       = []
takeL (suc n) []       = []
takeL (suc n) (x ∷ xs) = x ∷ takeL n xs
dropL zero    xs       = xs
dropL (suc n) []       = []
dropL (suc n) (x ∷ xs) = dropL n xs

nthL : ∀ {A : Set} → A → List A → Nat → A
nthL d []       _       = d
nthL d (x ∷ _)  zero    = x
nthL d (_ ∷ xs) (suc n) = nthL d xs n

setL : ∀ {A : Set} → List A → Nat → A → List A
setL []       _       _ = []
setL (_ ∷ xs) zero    y = y ∷ xs
setL (x ∷ xs) (suc n) y = x ∷ setL xs n y

-- positions where the flag holds
idxs : List Bool → List Nat
idxs bs = go 0 bs
  where
  go : Nat → List Bool → List Nat
  go k []           = []
  go k (true ∷ bs)  = k ∷ go (suc k) bs
  go k (false ∷ bs) = go (suc k) bs

mapMʳ : ∀ {A B : Set} → (A → Res B) → List A → Res (List B)
mapMʳ f []       = ok []
mapMʳ f (x ∷ xs) = f x >>=ʳ λ y → mapMʳ f xs >>=ʳ λ ys → ok (y ∷ ys)

------------------------------------------------------------------------
-- Trees: raising locally maximal positions, doubling one.

mutual
  raiseL : List Bool → List Tree → List Tree × List Bool
  raiseL bs []                   = [] , bs
  raiseL []       (node [] ∷ ts) = let r = raiseL [] ts in (node [] ∷ fst r) , snd r
  raiseL (b ∷ bs) (node [] ∷ ts) =
    let r = raiseL bs ts in ((if b then node (node [] ∷ []) else node []) ∷ fst r) , snd r
  raiseL bs (node (c ∷ cs) ∷ ts) =
    let r₁ = raiseL bs (c ∷ cs) ; r₂ = raiseL (snd r₁) ts in (node (fst r₁) ∷ fst r₂) , snd r₂

raiseT : List Bool → Tree → Tree
raiseT []      (node [])       = node []
raiseT (b ∷ _) (node [])       = if b then node (node [] ∷ []) else node []
raiseT bs      (node (t ∷ ts)) = node (fst (raiseL bs (t ∷ ts)))

mutual
  dblL : List Bool → List Tree → List Tree × List Bool
  dblL bs []                   = [] , bs
  dblL []       (node [] ∷ ts) = let r = dblL [] ts in (node [] ∷ fst r) , snd r
  dblL (b ∷ bs) (node [] ∷ ts) =
    let r = dblL bs ts in (if b then (node [] ∷ node [] ∷ fst r) else (node [] ∷ fst r)) , snd r
  dblL bs (node (c ∷ cs) ∷ ts) =
    let r₁ = dblL bs (c ∷ cs) ; r₂ = dblL (snd r₁) ts in (node (fst r₁) ∷ fst r₂) , snd r₂

dblT : List Bool → Tree → Tree
dblT bs (node []) = node []
dblT bs (node (t ∷ ts)) = node (fst (dblL bs (t ∷ ts)))

flagAt : Nat → Nat → List Bool
flagAt zero    i       = []
flagAt (suc n) zero    = true ∷ flagAt n 99999
flagAt (suc n) (suc i) = false ∷ flagAt n i

------------------------------------------------------------------------
-- Terms.

mutual
  depTm : (Nat → Bool) → Tm → Bool
  depTm d (var i)     = d i
  depTm d (coh _ _ σ) = depSub d σ
  depTm d (cst ())

  depSub : (Nat → Bool) → Sub → Bool
  depSub d ⟨⟩       = false
  depSub d (σ ,ₛ t) = depSub d σ ∨ depTm d t

vars : List Nat → List Tm
vars = mapL var

-- Re-apply the coherence (P, A) with tree T to new images of its
-- locally maximal variables.
reapply : Ctx → Ctx → Ty → Tree → List Tm → Maybe Tm
reapply Γ P A T args = zipA (tops T) args >>= λ top → fill Γ P top >>= λ σ → just (coh P A σ)

------------------------------------------------------------------------
-- The lift.

record Env : Set where
  constructor mkEnv
  field
    ctx   : Ctx
    isDep : Nat → Bool
    ren   : Nat → Nat
    lv    : Nat → Maybe Tm
open Env

hdM : List Tm → Maybe Tm
hdM []      = nothing
hdM (x ∷ _) = just x

lastL : Tm → List Tm → Tm
lastL d []       = d
lastL d (x ∷ []) = x
lastL d (_ ∷ x ∷ xs) = lastL d (x ∷ xs)

zipB : List Bool → List Tm → List (Bool × Tm)
zipB (b ∷ bs) (x ∷ xs) = (b , x) ∷ zipB bs xs
zipB _        _        = []

bnd : (Ctx → Tm → Maybe Tm) → Ctx → Bool × Tm → Tm
bnd f P (false , v) = v
bnd f P (true  , v) with f P v
... | just u  = u
... | nothing = var 999999

-- In P^ = ctxOf (raiseT ds T): the minus/plus copies of the raised
-- positions are the source/target of the new top variables.
levelOf : Tm → Nat
levelOf (var i) = i
levelOf _       = 999999

raised : Ctx → List Bool → List Nat → List (Nat × Nat × Nat)
raised P^ (true ∷ ds) (v ∷ th) =
  (levelOf (bnd srcOf P^ (true , var v)) , levelOf (bnd tgtOf P^ (true , var v)) , v) ∷ raised P^ ds th
raised P^ (false ∷ ds) (_ ∷ th) = raised P^ ds th
raised P^ _ _ = []

isMin : Ctx → List Bool → List Nat → Nat → Bool
isMin P^ ds th i = anyL (λ r → fst r ==ℕ i) (raised P^ ds th)

toPlus : Ctx → List Bool → List Nat → Nat → Nat
toPlus P^ ds th i = go (raised P^ ds th)
  where
  go : List (Nat × Nat × Nat) → Nat
  go []                  = i
  go ((m , p , _) ∷ rs)  = if m ==ℕ i then p else go rs

lvMin : Ctx → List Bool → List Nat → Nat → Maybe Tm
lvMin P^ ds th i = go (raised P^ ds th)
  where
  go : List (Nat × Nat × Nat) → Maybe Tm
  go []                  = nothing
  go ((m , _ , v) ∷ rs)  = if m ==ℕ i then just (var v) else go rs

-- The coherence (P, A, T) applied with its top position i raised by
-- one dimension: W(x) for an (d+1)-cell x, as the composite over the
-- raised tree of type W(∂⁻x) → W(∂⁺x).
raiseApply : Ctx → Ctx → Ty → Tree → List Tm → Nat → Tm → Maybe Tm
raiseApply Γ P A T args i x =
  let T^ = raiseT (flagAt (lenL args) i) T
      P^ = ctxOf T^
      th = vars (tops T^)
      V  = nthL (var 0) th i
  in srcOf P^ V >>= λ V⁻ → tgtOf P^ V >>= λ V⁺ →
     reapply P^ P A T (setL th i V⁻) >>= λ s →
     reapply P^ P A T (setL th i V⁺) >>= λ u →
     tyOf P^ s >>= λ B →
     zipA (tops T^) (setL args i x) >>= λ top → fill Γ P^ top >>= λ σ →
     just (coh P^ (arr B s u) σ)

module _ (o : Bool) where

  -- the two sides of a square
  sqSides : Ctx → Tm → Tm → Tm → Tm → Maybe (Tm × Tm)
  sqSides Γ Ls c bc Lt =
    vcomp Γ (Ls ∷ bc ∷ []) >>= λ x → vcomp Γ (c ∷ Lt ∷ []) >>= λ y →
    just (if o then (x , y) else (y , x))

  -- Functoriality of a whiskering coherence (P, A, T), at top position
  -- i, in a vertical composite there:
  --   dir = true : W p ; W q → W (p ; q),   dir = false: the reverse.
  funct : Bool → Ctx → Ctx → Ty → Tree → Nat → List Tm → Tm → Tm → Maybe Tm
  funct dir Γ P A T i args p q =
    let n  = lenL args
        T² = dblT (flagAt n i) T
        P² = ctxOf T²
        ts = vars (tops T²)
        pre = takeL i ts ; vp = nthL (var 0) ts i ; vq = nthL (var 0) ts (suc i)
        post = dropL (suc (suc i)) ts
    in reapply P² P A T (pre ++ vp ∷ post) >>= λ Wp →
       reapply P² P A T (pre ++ vq ∷ post) >>= λ Wq →
       vcomp P² (vp ∷ vq ∷ []) >>= λ pq →
       reapply P² P A T (pre ++ pq ∷ post) >>= λ Wpq →
       vcomp P² (Wp ∷ Wq ∷ []) >>= λ l →
       tyOf P² l >>= λ B →
       zipA (tops T²) (takeL i args ++ p ∷ q ∷ dropL (suc i) args) >>= λ top →
       fill Γ P² top >>= λ σ →
       just (coh P² (if dir then arr B l Wpq else arr B Wpq l) σ)

  mutual
    lift : Nat → Env → Tm → Res Tm
    lift zero    e t = err "fuel"
    lift (suc n) e (var i) with lv e i
    ... | just u  = ok u
    ... | nothing = err ("no lift for var " <> primShowNat i)
    lift (suc n) e (cst ())
    lift (suc n) e t@(coh P A σ) =
      fromM "treeOf" (treeOf P) >>=ʳ λ T →
      let Γ    = ctx e
          d    = isDep e
          args = mapL (lookupₛ σ) (tops T)
          ds   = mapL (depTm d) args
          sq   = λ a → depTm d (srcT Γ a)
          sqs  = mapL (λ a → depTm d a ∧ sq a) args
      in guardʳ "lift: independent term" (anyL (λ b → b) ds) >>=ʳ λ _ →
         if anyL (λ b → b) sqs
         then (if all (λ b → b) sqs ∧ chainOK Γ t args
               then paste n e args
               else whisk n e t P A T args sqs)
         else generic n e t P A T args ds

    srcT : Ctx → Tm → Tm
    srcT Γ a with srcOf Γ a
    ... | just s  = s
    ... | nothing = var 999999

    chainOK : Ctx → Tm → List Tm → Bool
    chainOK Γ t as@(_ ∷ _ ∷ _) with vcomp Γ as
    ... | just u  = u ==Tm t
    ... | nothing = false
    chainOK Γ t _ = false

    -- every travelling argument is a derivative
    generic : Nat → Env → Tm → Ctx → Ty → Tree → List Tm → List Bool → Res Tm
    generic n e t P A T args ds =
      let Γ  = ctx e
          d  = isDep e
          T^ = raiseT ds T
          P^ = ctxOf T^
          th = tops T^
          Vs = mapL var th
          mins = mapL (bnd srcOf P^) (zipB ds Vs)
          plss = mapL (bnd tgtOf P^) (zipB ds Vs)
      in fromM "generic: minus" (reapply P^ P A T mins) >>=ʳ λ t⁻ →
         fromM "generic: plus" (reapply P^ P A T plss) >>=ʳ λ t⁺ →
         mapMʳ (λ ba → if fst ba then lift n e (snd ba) else ok (snd ba)) (zipB ds args) >>=ʳ λ largs →
         fromM "generic: fill" (zipA th largs >>= fill Γ P^) >>=ʳ λ σ^ →
         (if depTm d (srcT Γ t)
          then (let e' = mkEnv P^ (isMin P^ ds th) (toPlus P^ ds th) (lvMin P^ ds th)
                in fromM "generic: src" (srcOf P^ t⁻) >>=ʳ λ s⁻ →
                   fromM "generic: tgt" (tgtOf P^ t⁻) >>=ʳ λ u⁻ →
                   lift n e' s⁻ >>=ʳ λ Ls → lift n e' u⁻ >>=ʳ λ Lt →
                   fromM "generic: square sides" (sqSides P^ Ls t⁻ t⁺ Lt) >>=ʳ λ lr →
                   fromM "generic: square type" (tyOf P^ (fst lr)) >>=ʳ λ B →
                   ok (arr B (fst lr) (snd lr)))
          else (fromM "generic: type" (tyOf P^ t⁻) >>=ʳ λ B → ok (arr B t⁻ t⁺))) >>=ʳ λ ty →
         ok (coh P^ ty σ^)

    -- a vertical chain of squares
    paste : Nat → Env → List Tm → Res Tm
    paste n e cs =
      let Γ = ctx e ; bcs = mapL (rnTm (ren e)) cs in
      fromM "paste: src" (hdM cs >>= srcOf Γ) >>=ʳ λ s₀ →
      lift n e s₀ >>=ʳ λ L₀ →
      mapMʳ (λ c → fromM "paste: tgt" (tgtOf Γ c) >>=ʳ lift n e) cs >>=ʳ λ Ls →
      mapMʳ (lift n e) cs >>=ʳ λ Sq →
      let Lall = L₀ ∷ Ls ; k = lenL cs in
      (if o
       then (fromM "paste: start" (regroup false Γ (L₀ ∷ []) bcs []) >>=ʳ λ r₀ →
             fwd Γ cs bcs Lall Sq 0 k (L₀ ∷ bcs) >>=ʳ λ steps →
             fromM "paste: end" (regroup true Γ [] cs (lastL L₀ Ls ∷ [])) >>=ʳ λ r₁ →
             ok (r₀ ∷ steps ++ r₁ ∷ []))
       else (fromM "paste: start" (regroup false Γ [] cs (lastL L₀ Ls ∷ [])) >>=ʳ λ r₀ →
             bwd Γ cs bcs Lall Sq k (cs ++ lastL L₀ Ls ∷ []) >>=ʳ λ steps →
             fromM "paste: end" (regroup true Γ (L₀ ∷ []) bcs []) >>=ʳ λ r₁ →
             ok (r₀ ∷ steps ++ r₁ ∷ []))) >>=ʳ λ pieces →
      fromM "paste: vcomp" (vcomp Γ pieces)

    -- step j (0-based) of the forward pasting: the chain is
    -- c₀ … c_{j−1}, L_j, bc_j … ; rewrite [L_j, bc_j] to [c_j, L_{j+1}].
    fwd : Ctx → List Tm → List Tm → List Tm → List Tm → Nat → Nat → List Tm → Res (List Tm)
    fwd Γ cs bcs Lall Sq j zero    ch = ok []
    fwd Γ cs bcs Lall Sq j (suc r) ch =
      let pre  = takeL j cs
          seg  = nthL (var 0) Lall j ∷ nthL (var 0) bcs j ∷ []
          seg' = nthL (var 0) cs j ∷ nthL (var 0) Lall (suc j) ∷ []
          post = dropL (suc j) bcs
      in fromM ("paste: fwd step " <> primShowNat j)
           (stepAt Γ pre seg post (nthL (var 0) Sq j) seg') >>=ʳ λ s →
         fwd Γ cs bcs Lall Sq (suc j) r (fst s) >>=ʳ λ rest → ok (snd s ∷ rest)

    -- backward pasting: steps j = k−1 … 0; the chain is
    -- c₀ … c_j, L_{j+1}, bc_{j+1} … ; rewrite [c_j, L_{j+1}] to [L_j, bc_j].
    bwd : Ctx → List Tm → List Tm → List Tm → List Tm → Nat → List Tm → Res (List Tm)
    bwd Γ cs bcs Lall Sq zero    ch = ok []
    bwd Γ cs bcs Lall Sq (suc j) ch =
      let pre  = takeL j cs
          seg  = nthL (var 0) cs j ∷ nthL (var 0) Lall (suc j) ∷ []
          seg' = nthL (var 0) Lall j ∷ nthL (var 0) bcs j ∷ []
          post = dropL (suc j) bcs
      in fromM ("paste: bwd step " <> primShowNat j)
           (stepAt Γ pre seg post (nthL (var 0) Sq j) seg') >>=ʳ λ s →
         bwd Γ cs bcs Lall Sq j (fst s) >>=ʳ λ rest → ok (snd s ∷ rest)

    -- a whiskering of a single square
    whisk : Nat → Env → Tm → Ctx → Ty → Tree → List Tm → List Bool → Res Tm
    whisk n e t P A T args sqs =
      let Γ = ctx e ; d = isDep e in
      oneIdx sqs >>=ʳ λ i →
      guardʳ "whisk: other travelling arguments"
        (lenL (idxs (mapL (depTm d) args)) ==ℕ 1) >>=ʳ λ _ →
      let Φ = nthL (var 0) args i ; bΦ = rnTm (ren e) Φ in
      fromM "whisk: src" (srcOf Γ Φ) >>=ʳ λ sΦ → fromM "whisk: tgt" (tgtOf Γ Φ) >>=ʳ λ tΦ →
      lift n e sΦ >>=ʳ λ Ls → lift n e tΦ >>=ʳ λ Lt → lift n e Φ >>=ʳ λ LΦ →
      fromM "whisk: W(LΦ)" (raiseApply Γ P A T args i LΦ) >>=ʳ λ WL →
      let X₁ = if o then Ls else Φ  ; X₂ = if o then bΦ else Lt
          Y₁ = if o then Φ  else Ls ; Y₂ = if o then Lt else bΦ
      in fromM "whisk: merge" (funct true Γ P A T i args X₁ X₂) >>=ʳ λ m →
         fromM "whisk: split" (funct false Γ P A T i args Y₁ Y₂) >>=ʳ λ s →
         fromM "whisk: vcomp" (vcomp Γ (m ∷ WL ∷ s ∷ []))

    oneIdx : List Bool → Res Nat
    oneIdx bs with idxs bs
    ... | i ∷ [] = ok i
    ... | _      = err "whisk: not exactly one square argument"

