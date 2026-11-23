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
--   * two object marks, `iord` (inner letters invertible) and `ord`
--     (inner letters trivial), ord ⇒ iord;
--   * (COH-ord): a head whose objects are all `ord` is read with the
--     two-tier rules.
-- It proves, on head data as reported by the side-condition procedure
-- (no checker for V + S exists yet, ledger S3):
--   * the old rule accepts the E13 counterexample shape and the
--     repaired one rejects it                       (old-accepts, new-rejects)
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
--   * the operation case with iso-path connected: soundness from the
--     single per-letter hypothesis `letters`     (OpModel, sound-op)
------------------------------------------------------------------------
module CaTTExp.Uniform.MarksRepaired where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Gray.Marks ∅ using (IP; ip; jinv; jps; jpss; grayInv; grayPs)
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
-- Head data.

data LKind : Set where
  grayL cylL joinL : LKind

-- One outer top letter of the designated lift.
record TopL : Set where
  constructor topL
  field
    kind     : LKind
    pure     : Bool                -- operands are generators of Γ
    factors  : List (Nat × Nat)    -- (i): the factors of its Gray cell
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

-- (OP-inv_S′)(a′) for one letter
kindInv : Setting → Head → List Comp → TopL → Bool
kindInv S h cs ℓ with kind ℓ
... | grayL = grayInv (facs cs (factors ℓ))
... | cylL  = jinv (jdg (nthC (mover ℓ) cs))
... | joinL = jinv (jdg (nthC (mover ℓ) cs))
              ∧ (iordTgt h cs ∨ (if leftSide ℓ then innerLaw S else rSplit S))

letterInv : Setting → Head → List Comp → TopL → Bool
letterInv S h cs ℓ = pure ℓ ∧ kindInv S h cs ℓ

-- (OP-ps_S′): case (i) may use ps* instead of inv
letterPs : Setting → Head → List Comp → TopL → Bool
letterPs S h cs ℓ with kind ℓ
... | grayL = pure ℓ ∧ grayPs (facs cs (factors ℓ))
... | _     = letterInv S h cs ℓ

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
psV S h cs =
  isOp (case h) ∧ all (letterPs S h cs) (liftTops h) ∧ innerOK h cs      -- (OP-ps_S′)

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
           (topL cylL false ((3 , 3) ∷ (1 , 4) ∷ []) 3 true ∷ [])
           false nothing 2 (0 ∷ 1 ∷ 2 ∷ [])

ezb-cs : List Comp
ezb-cs = obj ∷ obj ∷ obj ∷ idc ∷ unm ∷ []

old-accepts : invOld (setting true true) ezb ezb-cs ≡ true
old-accepts = refl

new-rejects : invU (setting true true) ezb ezb-cs ≡ false
new-rejects = refl

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
    letter   : ∀ ℓ → T (letterInv S h cs ℓ) → LetInv ℓ                  -- Thm 8.1 (i)–(iii)
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
-- category, and "invertible" is IsIso of its composite. What remains a
-- hypothesis is only the per-letter step: the premises of (OP-inv_S′)
-- make every letter image in p invertible (Thm 8.1 (i)–(iii) for the
-- outer letters, the iord reading for the inner ones), which includes
-- the decomposition of the image into those letters.

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
