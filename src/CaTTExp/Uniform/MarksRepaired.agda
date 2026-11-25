------------------------------------------------------------------------
-- The repaired uniform marks (ledger E14(a); notes/uniform-marks.md §8.2,
-- notes/ord-recovers-two-tier.md §1, §6; spec §3.6).
--
-- CaTTExp.Uniform.Marks encodes the first version, (OP-inv_S), whose
-- premise reads the Gray generator g[γ]. The E13 answer shows that rule
-- unsound on free algebras (hypothesis (IL) is false). This module
-- encodes the repaired rules:
--   * (OP-inv_S′)/(OP-ps_S′): premises on each top letter of the
--     designated lift, which must be operand-pure and of kind
--     (i) Gray cell, (ii) cylinder, (iii) binary join h(A, B);
--   * the factor rules for a Gray cell of kind (i) after the r2 answer
--     (E14(b), uniform-marks.md §8.6): (INV-fac) carries criterion (1)
--     on the bracketing tree, (PS-fac) is kept only for a binary pair
--     with the ps* factor last, and the ps* branch of (OP-ps_S′) is
--     removed                              (crit, crit-sound, crit-complete, grayInvU)
--   * two object marks, `iord` (inner letters invertible) and `ord`
--     (inner letters trivial), ord ⇒ iord;
--   * (COH-ord): a head whose objects are all `ord` is read with the
--     two-tier rules.
-- It proves, on head data as reported by the side-condition procedure
-- (no checker for V + S exists yet, ledger S3):
--   * the old rule accepts the E13 counterexample shape and the
--     repaired one rejects it                       (old-accepts, new-rejects)
--   * the pre-r2 rule accepts the (2, 2) shape, the right-bracketed
--     (2, 1, 1) shape and the (2, 2, 2) ps* shape, and the current rule
--     rejects all three; (2, 1) and left-bracketed (2, 1, 1) pass
--                                                    (*-22, *-211, *-222)
--   * uniform ⇒ two-tier for operation-case heads, given the
--     projection data                                (uniform-⊆-two-tier′)
--   * `iord` on the target suffices for (ORD)       (iord-ORD)
--   * with every object `ord`, the rules are the two-tier ones
--                                                    (coh-ord-two-tier)
--   * monotonicity in the setting and in the marks  (setting-mono′, mark-mono′)
--   * sound′ reduces soundness to the paper theorems given as fields of
--     Sem′ (uniform-marks.md 4.3, 4.4, 8.1; ord-recovers-two-tier.md
--     2.2/2.3; and `compose` = decomposition of the coherence image into
--     the letters of its lift plus Lemma 4.1). Inv, LetInv and InnInv
--     are abstract, so sound′ is a case dispatch over those fields.
--     None of the fields is (IL).                     (sound′)
--   * the composite step (Lemma 4.1) and the join step (§4.6), proved
--     separately over an abstract category      (iso-path, join-iso)
--   * the operation case with iso-path connected   (OpModel, sound-op).
--     Two inputs remain unchecked: (1) that the coherence's image is
--     pcomp p for the lift's letter images (p is a free field, not tied
--     to liftTops h, so OpModel can be inhabited with p = nil), and
--     (2) `letters`, the per-letter step.
------------------------------------------------------------------------
module CaTTExp.Uniform.MarksRepaired where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Gray.Marks ∅ using (IP; ip; jinv; jps; jpss; pos; grayInv; grayPs)
open import CaTTExp.Gray.Support ∅ using (map)
open import CaTTExp.Uniform.Marks
  using (Setting; setting; innerLaw; rSplit; _≤S_;
         GCase; coherenceC; innerC; grayOpC; isCoh; isInner; isOp;
         ∨-introl; ∨-intror; ∨-elim; ∨-false; false-∨; ∧-intro; fstT; sndT)

------------------------------------------------------------------------
-- Object marks.

data OMark : Set where
  noM iordM ordM : OMark

isI isO : OMark → Bool
isI noM   = false
isI iordM = true
isI ordM  = true
isO ordM  = true
isO _     = false

ord⇒iord : ∀ m → T (isO m) → T (isI m)
ord⇒iord ordM _ = tt

-- A substitution may send a variable marked m to one marked m′ when m′
-- is at least as strong.
_≼_ : OMark → OMark → Bool
noM   ≼ _     = true
iordM ≼ m′    = isI m′
ordM  ≼ m′    = isO m′

record Comp : Set where
  constructor comp
  field
    jdg : IP
    om  : OMark
open Comp public

nthC : Nat → List Comp → Comp
nthC _       []       = comp (ip false false false) noM
nthC zero    (c ∷ _)  = c
nthC (suc n) (_ ∷ cs) = nthC n cs

facs : List Comp → List (Nat × Nat) → List (Nat × IP)
facs cs g = map (λ x → fst x , jdg (nthC (snd x) cs)) g

------------------------------------------------------------------------
-- The factor rules over V + S (E14(b), uniform-marks.md §8.6).
--
-- A Gray cell G(x₁, …, xₙ) is lifted by a planar binary bracketing of its
-- consecutive factors, the one the head's forced value uses
-- (design-decisions.md §5). A leaf is (hom-dimension dᵢ, component
-- index of xᵢ); a node has the sum of the dimensions below it.

data BTree : Set where
  leaf : Nat → Nat → BTree
  node : BTree → BTree → BTree

tdim : BTree → Nat
tdim (leaf d _) = d
tdim (node l r) = tdim l + tdim r

leaves : BTree → List (Nat × Nat)
leaves (leaf d i) = (d , i) ∷ []
leaves (node l r) = leaves l ++ leaves r

big : Nat → Bool
big (suc (suc _)) = true
big _             = false

-- a node through which invertibility does not pass: two children of
-- dimension ≥ 2
blocks : BTree → BTree → Bool
blocks l r = big (tdim l) ∧ big (tdim r)

-- (INV-fac) with criterion (1), as a Boolean: some leaf with dᵢ ≥ 1 and
-- xᵢ[γ] inv such that no node on its path to the root blocks.
crit : List Comp → BTree → Bool
crit cs (leaf d i) = pos d ∧ jinv (jdg (nthC i cs))
crit cs (node l r) = not (blocks l r) ∧ (crit cs l ∨ crit cs r)

-- Criterion (1) as stated, per leaf.
data Pos : BTree → Set where
  here : ∀ {d i} → Pos (leaf d i)
  inL  : ∀ {l r} → Pos l → Pos (node l r)
  inR  : ∀ {l r} → Pos r → Pos (node l r)

clear : ∀ {t} → Pos t → Bool
clear here            = true
clear (inL {l} {r} p) = not (blocks l r) ∧ clear p
clear (inR {l} {r} p) = not (blocks l r) ∧ clear p

leafOK : List Comp → ∀ {t} → Pos t → Bool
leafOK cs (here {d} {i}) = pos d ∧ jinv (jdg (nthC i cs))
leafOK cs (inL p)        = leafOK cs p
leafOK cs (inR p)        = leafOK cs p

Crit1 : List Comp → BTree → Set
Crit1 cs t = Σ (Pos t) (λ p → T (clear p) × T (leafOK cs p))

private
  upL : ∀ cs {l r} → T (not (blocks l r)) → Crit1 cs l → Crit1 cs (node l r)
  upL cs {l} {r} nb (p , c , o) = inL p , ∧-intro {not (blocks l r)} nb c , o

  upR : ∀ cs {l r} → T (not (blocks l r)) → Crit1 cs r → Crit1 cs (node l r)
  upR cs {l} {r} nb (p , c , o) = inR p , ∧-intro {not (blocks l r)} nb c , o

crit-sound : ∀ cs t → T (crit cs t) → Crit1 cs t
crit-sound cs (leaf d i) q = here , tt , q
crit-sound cs (node l r) q =
  ∨-elim (crit cs l) (crit cs r)
    (λ x → upL cs nb (crit-sound cs l x))
    (λ x → upR cs nb (crit-sound cs r x))
    (sndT (not (blocks l r)) q)
  where nb = fstT (not (blocks l r)) q

crit-complete : ∀ cs t → Crit1 cs t → T (crit cs t)
crit-complete cs (leaf d i) (here , _ , o) = o
crit-complete cs (node l r) (inL p , c , o) =
  ∧-intro {not (blocks l r)} (fstT (not (blocks l r)) c)
    (∨-introl (crit cs r) (crit-complete cs l (p , sndT (not (blocks l r)) c , o)))
crit-complete cs (node l r) (inR p , c , o) =
  ∧-intro {not (blocks l r)} (fstT (not (blocks l r)) c)
    (∨-intror (crit cs l) (crit-complete cs r (p , sndT (not (blocks l r)) c , o)))

-- (INV-obj): no positive factor, every factor inv.
objInv : List Comp → BTree → Bool
objInv cs t = all (λ x → not (pos (fst x)) ∧ jinv (jdg (nthC (snd x) cs))) (leaves t)

-- (PS-fac), kept only where it is the definition of ps*: exactly two
-- factors, both positive, the later one ps*.
psBin : List Comp → BTree → Bool
psBin cs (node (leaf d₁ _) (leaf d₂ j)) = pos d₁ ∧ pos d₂ ∧ jpss (jdg (nthC j cs))
psBin cs _                              = false

-- g[γ] inv for a Gray cell over V + S.
grayInvU : List Comp → BTree → Bool
grayInvU cs t = crit cs t ∨ objInv cs t ∨ psBin cs t

------------------------------------------------------------------------
-- Head data.

data LKind : Set where
  grayL cylL joinL : LKind

-- One outer top letter of the designated lift.
record TopL : Set where
  constructor topL
  field
    kind     : LKind
    pure     : Bool                -- operands are generators of Γ
    tree     : BTree               -- (i): its Gray cell, bracketed
    mover    : Nat                 -- (ii): moving input; (iii): A
    leftSide : Bool                -- (iii): the A-cylinder is the left
                                   --        input of ῑ₋ (left split)
open TopL public

record Head : Set where
  constructor head
  field
    case     : GCase
    grayTops : List (List (Nat × Nat))  -- TopGray(Γ), for two-tier
    liftTops : List TopL                -- outer top letters of the lift
    innerTop : Bool                     -- an inner top letter exists
    elemIC   : Maybe (Nat × Nat)        -- elementary inner interchanger
    tgt      : Nat                      -- index of aₙ
    objs     : List Nat                 -- indices of a₀ … aₙ
open Head public

iordTgt : Head → List Comp → Bool
iordTgt h cs = isI (om (nthC (tgt h) cs))

allOrd : Head → List Comp → Bool
allOrd h cs = all (λ i → isO (om (nthC i cs))) (objs h)

innFac : Setting → Maybe (Nat × Nat) → List Comp → Bool
innFac S nothing        cs = false
innFac S (just (l , r)) cs =
  (innerLaw S ∧ jinv (jdg (nthC l cs))) ∨ (rSplit S ∧ jinv (jdg (nthC r cs)))

innerOK : Head → List Comp → Bool
innerOK h cs = not (innerTop h) ∨ iordTgt h cs

-- (OP-inv_S′)(a′) for one letter; case (i) uses the V + S factor rules
kindInv : Setting → Head → List Comp → TopL → Bool
kindInv S h cs ℓ with kind ℓ
... | grayL = grayInvU cs (tree ℓ)
... | cylL  = jinv (jdg (nthC (mover ℓ) cs))
... | joinL = jinv (jdg (nthC (mover ℓ) cs))
              ∧ (iordTgt h cs ∨ (if leftSide ℓ then innerLaw S else rSplit S))

letterInv : Setting → Head → List Comp → TopL → Bool
letterInv S h cs ℓ = pure ℓ ∧ kindInv S h cs ℓ

-- The pre-r2 version (E14(a)), for comparison: case (i) used the
-- two-tier factor rules on the unbracketed factors, and (OP-ps_S′) had
-- a ps* branch in case (i).
kindInv₀ : Setting → Head → List Comp → TopL → Bool
kindInv₀ S h cs ℓ with kind ℓ
... | grayL = grayInv (facs cs (leaves (tree ℓ)))
... | _     = kindInv S h cs ℓ

letterInv₀ letterPs₀ : Setting → Head → List Comp → TopL → Bool
letterInv₀ S h cs ℓ = pure ℓ ∧ kindInv₀ S h cs ℓ
letterPs₀ S h cs ℓ with kind ℓ
... | grayL = pure ℓ ∧ grayPs (facs cs (leaves (tree ℓ)))
... | _     = letterInv₀ S h cs ℓ

-- the two-tier rules on the projected head
invT psT : Head → List Comp → Bool
invT h cs = isCoh (case h) ∨ isInner (case h)
          ∨ (isOp (case h) ∧ all (λ g → grayInv (facs cs g)) (grayTops h))
psT h cs = isOp (case h) ∧ all (λ g → grayPs (facs cs g)) (grayTops h)

-- the uniform rules without (COH-ord)
invV psV : Setting → Head → List Comp → Bool
invV S h cs =
     isCoh (case h)                                                     -- (COH-inv)
  ∨ (isInner (case h) ∧ (iordTgt h cs ∨ innFac S (elemIC h) cs))        -- (ORD), (INN-fac_S)
  ∨ (isOp (case h) ∧ all (letterInv S h cs) (liftTops h) ∧ innerOK h cs) -- (OP-inv_S′)
-- (OP-ps_S′) without the ps* branch: the premises of (OP-inv_S′). ps
-- enters case (i) only through psBin, the definition of ps*.
psV S h cs =
  isOp (case h) ∧ all (letterInv S h cs) (liftTops h) ∧ innerOK h cs     -- (OP-ps_S′)

invV₀ psV₀ : Setting → Head → List Comp → Bool
invV₀ S h cs = isOp (case h) ∧ all (letterInv₀ S h cs) (liftTops h) ∧ innerOK h cs
psV₀  S h cs = isOp (case h) ∧ all (letterPs₀ S h cs) (liftTops h) ∧ innerOK h cs

-- with (COH-ord): an all-ord head is a two-tier head
invU psU : Setting → Head → List Comp → Bool
invU S h cs = if allOrd h cs then invT h cs else invV S h cs
psU  S h cs = if allOrd h cs then psT h cs else psV S h cs

-- the first version, for comparison: premise on the Gray generators
invOld : Setting → Head → List Comp → Bool
invOld S h cs =
     isCoh (case h)
  ∨ (isInner (case h) ∧ (iordTgt h cs ∨ innFac S (elemIC h) cs))
  ∨ (isOp (case h) ∧ all (λ g → grayInv (facs cs g)) (grayTops h) ∧ innerOK h cs)

------------------------------------------------------------------------
-- The E13 counterexample shape: one outer top letter E(Z, b), a
-- cylinder whose moving operand Z is not a generator; its Gray cell
-- G(x, b) has been substituted to an identity, which the two-tier rules
-- judge inv. Components: 0 = a₀, 1 = a₁, 2 = a₂ (objects, unmarked),
-- 3 = x (sent to an identity: inv), 4 = b.

private
  idc unm obj : Comp
  idc = comp (ip true true true) noM
  unm = comp (ip false false false) noM
  obj = comp (ip false false false) noM

ezb : Head
ezb = head grayOpC (((3 , 3) ∷ (1 , 4) ∷ []) ∷ [])
           (topL cylL false (node (leaf 3 3) (leaf 1 4)) 3 true ∷ [])
           false nothing 2 (0 ∷ 1 ∷ 2 ∷ [])

ezb-cs : List Comp
ezb-cs = obj ∷ obj ∷ obj ∷ idc ∷ unm ∷ []

old-accepts : invOld (setting true true) ezb ezb-cs ≡ true
old-accepts = refl

new-rejects : invU (setting true true) ezb ezb-cs ≡ false
new-rejects = refl

------------------------------------------------------------------------
-- The r2 shapes (uniform-marks.md §8.6). One pure Gray top letter on
-- three unmarked objects (components 0, 1, 2) and factors from
-- component 3 on. `iv` is an inv factor, `ps` a ps* one.

private
  iv ps : Comp
  iv = comp (ip true true true) noM
  ps = comp (ip false true true) noM

  grayHead : BTree → Head
  grayHead t = head grayOpC (leaves t ∷ [])
                    (topL grayL true t 0 true ∷ []) false nothing 2 (0 ∷ 1 ∷ 2 ∷ [])

  S₂ : Setting
  S₂ = setting true true

-- (2, 2), first factor inv: W(A, B). Fails in every setting.
t22 : BTree
t22 = node (leaf 2 3) (leaf 2 4)

old-accepts-22 : invV₀ S₂ (grayHead t22) (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ []) ≡ true
old-accepts-22 = refl
new-rejects-22 : invU S₂ (grayHead t22) (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ []) ≡ false
new-rejects-22 = refl

-- (2, 1) and (1, 2): pass, from either factor.
new-accepts-21 : invU S₂ (grayHead (node (leaf 2 3) (leaf 1 4)))
                         (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ []) ≡ true
new-accepts-21 = refl
new-accepts-12 : invU S₂ (grayHead (node (leaf 1 3) (leaf 2 4)))
                         (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ []) ≡ true
new-accepts-12 = refl

-- (2, 1, 1), first factor inv: the bracketing matters.
t211L t211R : BTree
t211L = node (node (leaf 2 3) (leaf 1 4)) (leaf 1 5)
t211R = node (leaf 2 3) (node (leaf 1 4) (leaf 1 5))     -- W(A, χ(b, c))

new-accepts-211L : invU S₂ (grayHead t211L) (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ unm ∷ []) ≡ true
new-accepts-211L = refl
old-accepts-211R : invV₀ S₂ (grayHead t211R) (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ unm ∷ []) ≡ true
old-accepts-211R = refl
new-rejects-211R : invU S₂ (grayHead t211R) (obj ∷ obj ∷ obj ∷ iv ∷ unm ∷ unm ∷ []) ≡ false
new-rejects-211R = refl

-- (2, 2, 2), middle input ps*: the ps* factor rule, false in every
-- setting and for either bracketing.
t222L t222R : BTree
t222L = node (node (leaf 2 3) (leaf 2 4)) (leaf 2 5)
t222R = node (leaf 2 3) (node (leaf 2 4) (leaf 2 5))

old-ps-222 : (psV₀ S₂ (grayHead t222L) (obj ∷ obj ∷ obj ∷ unm ∷ ps ∷ unm ∷ []) ≡ true)
           × (psV₀ S₂ (grayHead t222R) (obj ∷ obj ∷ obj ∷ unm ∷ ps ∷ unm ∷ []) ≡ true)
old-ps-222 = refl , refl
new-ps-222 : (psU S₂ (grayHead t222L) (obj ∷ obj ∷ obj ∷ unm ∷ ps ∷ unm ∷ []) ≡ false)
           × (psU S₂ (grayHead t222R) (obj ∷ obj ∷ obj ∷ unm ∷ ps ∷ unm ∷ []) ≡ false)
new-ps-222 = refl , refl

-- A binary pair with the ps* factor last is still inv (definition of ps*).
new-ps-bin : invU S₂ (grayHead (node (leaf 2 3) (leaf 2 4)))
                     (obj ∷ obj ∷ obj ∷ unm ∷ ps ∷ []) ≡ true
new-ps-bin = refl

------------------------------------------------------------------------
-- (ORD) needs only iord on the target; ord on every object gives the
-- two-tier rules.

iord-ORD : ∀ S h cs → case h ≡ innerC → allOrd h cs ≡ false →
           T (iordTgt h cs) → T (invU S h cs)
iord-ORD S h cs c a o rewrite a | c = false-∨ _ (∨-introl _ o)

coh-ord-two-tier : ∀ S h cs → allOrd h cs ≡ true →
                   (invU S h cs ≡ invT h cs) × (psU S h cs ≡ psT h cs)
coh-ord-two-tier S h cs a rewrite a = refl , refl

------------------------------------------------------------------------
-- Uniform ⇒ two-tier. For the operation case this needs the projection
-- data: every top generator of U(Γ) is the Gray cell of some top letter
-- of the lift (π(c) = τ_Γ), and a letter judged inv makes its Gray cell
-- inv (cases (ii), (iii): an inv positive factor, (INV-fac)).

record Proj (S : Setting) (h : Head) (cs : List Comp) : Set where
  field
    covers : T (all (letterInv S h cs) (liftTops h)) →
             T (all (λ g → grayInv (facs cs g)) (grayTops h))

uniform-⊆-two-tier′ : ∀ S h cs → Proj S h cs → T (invU S h cs) → T (invT h cs)
uniform-⊆-two-tier′ S h cs P p with allOrd h cs
... | true  = p
... | false with case h
...   | coherenceC = tt
...   | innerC     = tt
...   | grayOpC    =
        Proj.covers P (fstT (all (letterInv S h cs) (liftTops h)) p)

------------------------------------------------------------------------
-- Monotonicity in the setting.

innFac-mono : ∀ {S S′} → S ≤S S′ → ∀ m cs → T (innFac S m cs) → T (innFac S′ m cs)
innFac-mono (il , rr) nothing cs ()
innFac-mono {S} {S′} (il , rr) (just (l , r)) cs p =
  ∨-elim (innerLaw S ∧ jinv (jdg (nthC l cs))) (rSplit S ∧ jinv (jdg (nthC r cs)))
    (λ q → ∨-introl _ (∧-intro (il (fstT (innerLaw S) q)) (sndT (innerLaw S) q)))
    (λ q → ∨-intror _ (∧-intro (rr (fstT (rSplit S) q)) (sndT (rSplit S) q)))
    p

private
  if-mono : ∀ (b : Bool) {x x′ y y′ : Bool} → (T x → T x′) → (T y → T y′) →
            T (if b then x else y) → T (if b then x′ else y′)
  if-mono true  f g = f
  if-mono false f g = g

  ∧-mono : ∀ {a a′ b b′} → (T a → T a′) → (T b → T b′) → T (a ∧ b) → T (a′ ∧ b′)
  ∧-mono {true} {a′} f g p = ∧-intro {a′} (f tt) (g p)

  all-mono : ∀ {A : Set} (p q : A → Bool) → (∀ x → T (p x) → T (q x)) →
             ∀ xs → T (all p xs) → T (all q xs)
  all-mono p q f []       _ = tt
  all-mono p q f (x ∷ xs) t =
    ∧-intro {q x} (f x (fstT (p x) t)) (all-mono p q f xs (sndT (p x) t))

kindInv-mono : ∀ {S S′} → S ≤S S′ → ∀ h cs ℓ → T (kindInv S h cs ℓ) → T (kindInv S′ h cs ℓ)
kindInv-mono le h cs ℓ p with kind ℓ
... | grayL = p
... | cylL  = p
kindInv-mono {S} {S′} (il , rr) h cs ℓ p | joinL =
  ∧-mono {jinv (jdg (nthC (mover ℓ) cs))} (λ x → x)
    (λ q → ∨-elim (iordTgt h cs) _ (∨-introl _)
             (λ r → ∨-intror (iordTgt h cs) (side (leftSide ℓ) r)) q) p
  where
    side : ∀ b → T (if b then innerLaw S else rSplit S) → T (if b then innerLaw S′ else rSplit S′)
    side true  = il
    side false = rr

setting-mono′ : ∀ {S S′} → S ≤S S′ → ∀ h cs → T (invU S h cs) → T (invU S′ h cs)
setting-mono′ {S} {S′} le h cs = if-mono (allOrd h cs) (λ x → x) vmono
  where
    lmono : ∀ ℓ → T (letterInv S h cs ℓ) → T (letterInv S′ h cs ℓ)
    lmono ℓ = ∧-mono {pure ℓ} (λ x → x) (kindInv-mono le h cs ℓ)
    vmono : T (invV S h cs) → T (invV S′ h cs)
    vmono p with case h
    ... | coherenceC = tt
    ... | innerC     =
          false-∨ _ (∨-elim (iordTgt h cs) (innFac S (elemIC h) cs) (∨-introl _)
            (λ q → ∨-intror (iordTgt h cs) (innFac-mono le (elemIC h) cs q)) (∨-false _ p))
    ... | grayOpC    =
          ∧-mono {all (letterInv S h cs) (liftTops h)} (all-mono _ _ lmono (liftTops h)) (λ x → x) p

------------------------------------------------------------------------
-- Soundness. The composite step (Lemma 4.1) and the join step (§4.6)
-- over an abstract category, in diagrammatic order.

record Cat : Set₁ where
  field
    Ob    : Set
    Hom   : Ob → Ob → Set
    id    : ∀ {a} → Hom a a
    _⨾_   : ∀ {a b c} → Hom a b → Hom b c → Hom a c
    idl   : ∀ {a b} (f : Hom a b) → id ⨾ f ≡ f
    idr   : ∀ {a b} (f : Hom a b) → f ⨾ id ≡ f
    assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d) →
            (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)

module CatFacts (C : Cat) where
  open Cat C

  record IsIso {a b} (f : Hom a b) : Set where
    constructor iso
    field
      inv  : Hom b a
      linv : f ⨾ inv ≡ id
      rinv : inv ⨾ f ≡ id

  iso-⨾ : ∀ {a b c} {f : Hom a b} {g : Hom b c} → IsIso f → IsIso g → IsIso (f ⨾ g)
  iso-⨾ {f = f} {g} (iso f′ fl fr) (iso g′ gl gr) = iso (g′ ⨾ f′) l r
    where
      l : (f ⨾ g) ⨾ (g′ ⨾ f′) ≡ id
      l = trans (assoc f g (g′ ⨾ f′))
          (trans (cong (f ⨾_) (sym (assoc g g′ f′)))
          (trans (cong (λ x → f ⨾ (x ⨾ f′)) gl)
          (trans (cong (f ⨾_) (idl f′)) fl)))
      r : (g′ ⨾ f′) ⨾ (f ⨾ g) ≡ id
      r = trans (assoc g′ f′ (f ⨾ g))
          (trans (cong (g′ ⨾_) (sym (assoc f′ f g)))
          (trans (cong (λ x → g′ ⨾ (x ⨾ g)) fr)
          (trans (cong (g′ ⨾_) (idl g)) gr)))

  iso-id : ∀ {a} → IsIso (id {a})
  iso-id = iso id (idl id) (idl id)

  -- a ∗-path of letters and its composite
  data Path : Ob → Ob → Set where
    nil  : ∀ {a} → Path a a
    cons : ∀ {a b c} → Hom a b → Path b c → Path a c

  pcomp : ∀ {a b} → Path a b → Hom a b
  pcomp nil        = id
  pcomp (cons f p) = f ⨾ pcomp p

  AllIso : ∀ {a b} → Path a b → Set
  AllIso nil        = ⊤
  AllIso (cons f p) = IsIso f × AllIso p

  -- Lemma 4.1: a path of invertible letters has an invertible composite
  iso-path : ∀ {a b} (p : Path a b) → AllIso p → IsIso (pcomp p)
  iso-path nil        _       = iso-id
  iso-path (cons f p) (i , is) = iso-⨾ i (iso-path p is)

  -- §4.6: r = h ⨾ i with r and i invertible makes h invertible
  join-iso : ∀ {a b c} (h : Hom a b) (i : Hom b c) (r : Hom a c) →
             r ≡ h ⨾ i → IsIso r → IsIso i → IsIso h
  join-iso h i r e ir (iso i′ il ir′) =
    subst IsIso hq (iso-⨾ ir (iso i ir′ il))
    where
      hq : r ⨾ i′ ≡ h
      hq = trans (cong (_⨾ i′) e)
           (trans (assoc h i i′) (trans (cong (h ⨾_) il) (idr h)))

-- Per-letter statements, each proved on paper in every algebra (no (IL)).
-- `LetInv ℓ` is "the image of letter ℓ is invertible" in a fixed model and
-- assignment respecting the marks; `Inv` is the same for the coherence.
record Sem′ (S : Setting) (h : Head) (cs : List Comp) : Set₁ where
  field
    Inv      : Set
    LetInv   : TopL → Set
    InnInv   : Set     -- every inner top letter's image is invertible
    coh-sem  : case h ≡ coherenceC → Inv                                -- Thm 4.3
    ord-sem  : case h ≡ innerC → T (iordTgt h cs) → Inv                 -- Thm 4.3 (iord reading)
    inn-sem  : case h ≡ innerC → T (innFac S (elemIC h) cs) → Inv       -- Thm 4.4 (InnerInv)
    two-sem  : T (allOrd h cs) → T (invT h cs) → Inv                    -- Thm 2.3 of ord-recovers-two-tier
    letter   : ∀ ℓ → T (letterInv S h cs ℓ) → LetInv ℓ                  -- Thm 8.1 (i)–(iii); in (i), §8.6 for crit/psBin
    innerTop : T (innerOK h cs) → InnInv                                -- (b): iord target
    compose  : (∀ ℓ → T (letterInv S h cs ℓ) → LetInv ℓ) →
               T (all (letterInv S h cs) (liftTops h)) → InnInv → Inv  -- Lemma 4.1 (iso-path)

sound′ : ∀ S h cs (M : Sem′ S h cs) → T (invU S h cs) → Sem′.Inv M
sound′ S h cs M p with allOrd h cs | Sem′.two-sem M
... | true  | two = two tt p
... | false | _ with case h | Sem′.coh-sem M | Sem′.ord-sem M | Sem′.inn-sem M
...   | coherenceC | c | _ | _ = c refl
...   | innerC     | _ | o | i =
        ∨-elim (iordTgt h cs) (innFac S (elemIC h) cs) (o refl) (i refl) (∨-false _ p)
...   | grayOpC    | _ | _ | _ =
        Sem′.compose M (Sem′.letter M)
          (fstT (all (letterInv S h cs) (liftTops h)) p)
          (Sem′.innerTop M (sndT (all (letterInv S h cs) (liftTops h)) p))

------------------------------------------------------------------------
-- Directed Eckmann–Hilton (spec §3.6 Example (a)) with the two marks.
-- Components: X, C, a, b; C is component 1.

private
  ehHead : Head
  ehHead = head innerC [] [] false (just (2 , 3)) 1 (0 ∷ 1 ∷ [])

  cI cO : Comp
  cI = comp (ip false false false) iordM
  cO = comp (ip false false false) ordM

eh-unmarked : invU (setting false false) ehHead (unm ∷ unm ∷ unm ∷ unm ∷ []) ≡ false
eh-unmarked = refl
eh-iord     : invU (setting false false) ehHead (unm ∷ cI ∷ unm ∷ unm ∷ []) ≡ true
eh-iord     = refl
eh-ord-C    : invU (setting false false) ehHead (unm ∷ cO ∷ unm ∷ unm ∷ []) ≡ true
eh-ord-C    = refl
eh-ord-all  : invU (setting false false) ehHead (cO ∷ cO ∷ unm ∷ unm ∷ []) ≡ true
eh-ord-all  = refl

------------------------------------------------------------------------
-- E14(d): the operation case with Lemma 4.1 connected. The model's
-- image of the designated lift is a path p of letter images in a
-- category, and "invertible" is IsIso of its composite. Unchecked:
-- (1) that p is the path of the lift's letter images (p is a free
-- field, not indexed by liftTops h); (2) `letters`, the premises of
-- (OP-inv_S′) make every letter image in p invertible (Thm 8.1
-- (i)–(iii) for the outer letters, the iord reading for the inner ones).

record OpModel (S : Setting) (h : Head) (cs : List Comp) : Set₁ where
  field
    C     : Cat
  open Cat C public
  open CatFacts C public
  field
    a b     : Ob
    p       : Path a b
    letters : T (all (letterInv S h cs) (liftTops h)) → T (innerOK h cs) → AllIso p

sound-op : ∀ S h cs (M : OpModel S h cs) → case h ≡ grayOpC → allOrd h cs ≡ false →
           T (invU S h cs) → OpModel.IsIso M (OpModel.pcomp M (OpModel.p M))
sound-op S h cs M c a q rewrite a | c =
  OpModel.iso-path M (OpModel.p M)
    (OpModel.letters M (fstT (all (letterInv S h cs) (liftTops h)) q)
                       (sndT (all (letterInv S h cs) (liftTops h)) q))
