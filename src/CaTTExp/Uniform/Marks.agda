------------------------------------------------------------------------
-- Invertibility marks over the uniform core V + S
-- (notes/uniform-marks.md §3, §5; spec/03-invertibility-markings.md §3.6).
--
-- No checker for the uniform side condition exists yet (ledger S3), so
-- this module takes the output of the side-condition procedure for one
-- coherence head as data (`Head`), and the judgments of the
-- substitution's components as data (`Comp`). On that data it defines
--   * the uniform rules: (COH-inv), (OP-inv_S), (OP-ps_S), (ORD),
--     (INN-fac_S), with the outer premise computed by the very same
--     functions `grayInv`, `grayPs` that the two-tier checker uses
--     (CaTTExp.Gray.Marks);
--   * the two-tier rules read on the projected head (Gray case only);
-- and proves
--   * uniform ⇒ two-tier, in every setting      (uniform-⊆-two-tier)
--   * with the target object `ord`, uniform = two-tier, in every
--     setting                                   (ord-covers-two-tier, ord-agrees)
--   * monotonicity in the setting                (setting-mono)
--   * non-collapse: an inner coherence with no `ord` and no switch is
--     not judged invertible                     (no-collapse)
--   * soundness of the decision procedure from the per-rule semantic
--     statements (`Sem`), and the (INN-fac) semantic statement itself
--     from CaTTExp.Uniform.InnerInv              (sound, innFac-sem)
-- The semantic statements other than (INN-fac) are hypotheses of
-- `sound` (fields of `Sem`); the note proves them on paper (Thm 4.3,
-- Thm 4.7, the latter for the model class 𝓜_S). They are not
-- postulated anywhere.
------------------------------------------------------------------------
module CaTTExp.Uniform.Marks where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Gray.Marks ∅ using (IP; ip; jinv; jps; jpss; grayInv; grayPs; pos)
open import CaTTExp.Gray.Support ∅ using (map)
open import CaTTExp.Uniform.InnerInv

------------------------------------------------------------------------
-- Settings: the two visible switches of spec §2.3.

record Setting : Set where
  constructor setting
  field
    innerLaw : Bool    -- left split of the inner interchanger
    rSplit   : Bool    -- right split R
open Setting public

_≤S_ : Setting → Setting → Set
S ≤S S′ = (T (innerLaw S) → T (innerLaw S′)) × (T (rSplit S) → T (rSplit S′))

------------------------------------------------------------------------
-- Data of one coherence head coh_{Γ,A}[γ], as the side-condition
-- procedure of V + S reports it.

-- Gray image of the designated lift c (notes §1, (F8)):
--   coherenceC : ⟦t⟧ = ⟦u⟧ in F_{V+S}(Γ), c an identity
--   innerC     : π(c) an identity, ⟦t⟧ ≠ ⟦u⟧ (an inner coherence)
--   grayOpC    : π(c) = τ_Γ (Gray operation case)
data GCase : Set where
  coherenceC innerC grayOpC : GCase

-- A component of γ, with its judgments, and whether it is an object
-- variable marked ord.
record Comp : Set where
  constructor comp
  field
    jdg : IP
    ord : Bool
open Comp public

nthC : Nat → List Comp → Comp
nthC _       []       = comp (ip false false false) false
nthC zero    (c ∷ _)  = c
nthC (suc n) (_ ∷ cs) = nthC n cs

record Head : Set where
  constructor head
  field
    case     : GCase
    -- TopGray(Γ): each top generator of U(Γ) as its factors
    -- (dimension dᵢ, index of xᵢ among γ's components)
    tops     : List (List (Nat × Nat))
    -- some lift has an inner letter of top dimension
    innerTop : Bool
    -- for the elementary inner interchanger head: indices of the
    -- left and right inputs
    elemIC   : Maybe (Nat × Nat)
    -- index of the 0-target object aₙ among γ's components
    tgt      : Nat
open Head public

isCoh isInner isOp : GCase → Bool
isCoh coherenceC = true
isCoh _          = false
isInner innerC   = true
isInner _        = false
isOp grayOpC     = true
isOp _           = false

facs : List Comp → List (Nat × Nat) → List (Nat × IP)
facs cs g = map (λ x → fst x , jdg (nthC (snd x) cs)) g

------------------------------------------------------------------------
-- The rules.

ordTgt : Head → List Comp → Bool
ordTgt h cs = ord (nthC (tgt h) cs)

-- (INN-fac_S)
innFac : Setting → Maybe (Nat × Nat) → List Comp → Bool
innFac S nothing        cs = false
innFac S (just (l , r)) cs =
  (innerLaw S ∧ jinv (jdg (nthC l cs))) ∨ (rSplit S ∧ jinv (jdg (nthC r cs)))

-- premise (b): inner top letters need the target ord
innerOK : Head → List Comp → Bool
innerOK h cs = not (innerTop h) ∨ ordTgt h cs

invU psU : Setting → Head → List Comp → Bool
invU S h cs =
     isCoh (case h)                                                     -- (COH-inv)
  ∨ (isInner (case h) ∧ (ordTgt h cs ∨ innFac S (elemIC h) cs))         -- (ORD), (INN-fac_S)
  ∨ (isOp (case h) ∧ all (λ g → grayInv (facs cs g)) (tops h)
                   ∧ innerOK h cs)                                      -- (OP-inv_S)
psU S h cs =
  isOp (case h) ∧ all (λ g → grayPs (facs cs g)) (tops h) ∧ innerOK h cs -- (OP-ps_S)

-- The two-tier rules on the projected head: in 𝔉 the Gray coherence
-- case (coherenceC or innerC) is CaTT's coherence case, and the Gray
-- operation case is read on the same top generators.
invT psT : Head → List Comp → Bool
invT h cs = isCoh (case h) ∨ isInner (case h)
          ∨ (isOp (case h) ∧ all (λ g → grayInv (facs cs g)) (tops h))
psT h cs = isOp (case h) ∧ all (λ g → grayPs (facs cs g)) (tops h)

------------------------------------------------------------------------
-- Boolean lemmas.

∨-introl : ∀ {a} b → T a → T (a ∨ b)
∨-introl {true} b _ = tt

∨-intror : ∀ a {b} → T b → T (a ∨ b)
∨-intror true  _ = tt
∨-intror false t = t

∨-elim : ∀ {A : Set} a b → (T a → A) → (T b → A) → T (a ∨ b) → A
∨-elim true  b f g t = f tt
∨-elim false b f g t = g t

∨-false : ∀ a → T (a ∨ false) → T a
∨-false true  _ = tt
∨-false false ()

false-∨ : ∀ a → T a → T (a ∨ false)
false-∨ true _ = tt

∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro {true} _ t = t

fstT : ∀ a {b} → T (a ∧ b) → T a
fstT true _ = tt

sndT : ∀ a {b} → T (a ∧ b) → T b
sndT true t = t

------------------------------------------------------------------------
-- Uniform ⇒ two-tier, in every setting (the marks-level form of S2).

uniform-⊆-two-tier-inv : ∀ S h cs → T (invU S h cs) → T (invT h cs)
uniform-⊆-two-tier-inv S (head coherenceC tops it e t) cs _ = tt
uniform-⊆-two-tier-inv S (head innerC tops it e t) cs _ = tt
uniform-⊆-two-tier-inv S (head grayOpC tops it e t) cs p =
  fstT (all (λ g → grayInv (facs cs g)) tops) p

uniform-⊆-two-tier-ps : ∀ S h cs → T (psU S h cs) → T (psT h cs)
uniform-⊆-two-tier-ps S (head grayOpC tops it e t) cs p =
  fstT (all (λ g → grayPs (facs cs g)) tops) p

------------------------------------------------------------------------
-- With the target ord, uniform = two-tier, in every setting.

ord-covers-two-tier-inv : ∀ S h cs → T (ordTgt h cs) → T (invT h cs) → T (invU S h cs)
ord-covers-two-tier-inv S (head coherenceC tops it e t) cs o _ = tt
ord-covers-two-tier-inv S (head innerC tops it e t) cs o _ =
  false-∨ _ (∨-introl _ o)
ord-covers-two-tier-inv S (head grayOpC tops it e t) cs o p =
  ∧-intro {all (λ g → grayInv (facs cs g)) tops} p (∨-intror (not it) o)

ord-covers-two-tier-ps : ∀ S h cs → T (ordTgt h cs) → T (psT h cs) → T (psU S h cs)
ord-covers-two-tier-ps S (head grayOpC tops it e t) cs o p =
  ∧-intro {all (λ g → grayPs (facs cs g)) tops} p (∨-intror (not it) o)

------------------------------------------------------------------------
-- Monotonicity in the setting: switching laws on never loses a judgment
-- (imports run upwards, spec §2.3).

innFac-mono : ∀ {S S′} → S ≤S S′ → ∀ m cs → T (innFac S m cs) → T (innFac S′ m cs)
innFac-mono {S} {S′} (il , rr) nothing cs ()
innFac-mono {S} {S′} (il , rr) (just (l , r)) cs p =
  ∨-elim (innerLaw S ∧ jinv (jdg (nthC l cs))) (rSplit S ∧ jinv (jdg (nthC r cs)))
    (λ q → ∨-introl _ (∧-intro (il (fstT (innerLaw S) q)) (sndT (innerLaw S) q)))
    (λ q → ∨-intror _ (∧-intro (rr (fstT (rSplit S) q)) (sndT (rSplit S) q)))
    p

setting-mono : ∀ {S S′} → S ≤S S′ → ∀ h cs → T (invU S h cs) → T (invU S′ h cs)
setting-mono le (head coherenceC tops it e t) cs p = tt
setting-mono {S} {S′} le (head innerC tops it e t) cs p =
  false-∨ _ (∨-elim (ord (nthC t cs)) (innFac S e cs) (λ o → ∨-introl _ o)
         (λ q → ∨-intror (ord (nthC t cs)) (innFac-mono le e cs q)) (∨-false _ p))
setting-mono le (head grayOpC tops it e t) cs p = p

------------------------------------------------------------------------
-- Non-collapse: without ord on the target and with no switch on, no
-- rule makes an inner coherence invertible.

no-collapse : ∀ h cs → case h ≡ innerC → ord (nthC (tgt h) cs) ≡ false →
              invU (setting false false) h cs ≡ false
no-collapse (head innerC tops it nothing t) cs refl o rewrite o = refl
no-collapse (head innerC tops it (just _) t) cs refl o rewrite o = refl

------------------------------------------------------------------------
-- Soundness of the decision procedure from the per-rule semantic
-- statements. `Inv` is "the interpretation of the coherence is
-- invertible" in a fixed model under a fixed assignment respecting the
-- marks; each field is one rule's soundness statement for this head.

record Sem (S : Setting) (h : Head) (cs : List Comp) : Set₁ where
  field
    Inv      : Set
    coh-sem  : case h ≡ coherenceC → Inv                         -- Thm 4.3
    ord-sem  : case h ≡ innerC → T (ordTgt h cs) → Inv            -- Thm 4.3
    inn-sem  : case h ≡ innerC → T (innFac S (elemIC h) cs) → Inv -- Thm 4.4 (see innFac-sem)
    op-sem   : case h ≡ grayOpC → T (all (λ g → grayInv (facs cs g)) (tops h)) →
               T (innerOK h cs) → Inv                             -- Thm 4.7 (model class 𝓜_S)

sound : ∀ S h cs (M : Sem S h cs) → T (invU S h cs) → Sem.Inv M
sound S (head coherenceC tops it e t) cs M p = Sem.coh-sem M refl
sound S (head innerC tops it e t) cs M p =
  ∨-elim (ord (nthC t cs)) (innFac S e cs) (Sem.ord-sem M refl) (Sem.inn-sem M refl) (∨-false _ p)
sound S (head grayOpC tops it e t) cs M p =
  Sem.op-sem M refl (fstT (all (λ g → grayInv (facs cs g)) tops) p)
                    (sndT (all (λ g → grayInv (facs cs g)) tops) p)

------------------------------------------------------------------------
-- The (INN-fac) semantic statement, discharged by InnerInv: in a slice
-- interpreting the elementary interchanger head with inputs F, G, if
-- the setting's switches hold as laws of the model and the marked
-- inputs are invertible, ι(F, G) is invertible.

record ElemModel (S : Setting) : Set₁ where
  field
    sl : Slice
  open Slice sl public
  field
    f f′ g g′ : _
    F : A2 f f′
    G : B2 g g′
    leftLaw  : T (innerLaw S) → LeftSplit sl
    rightLaw : T (rSplit S) → RightSplit sl

innFac-sem : ∀ {S} (M : ElemModel S) l r cs →
             (T (jinv (jdg (nthC l cs))) → ElemModel.InvA M (ElemModel.F M)) →
             (T (jinv (jdg (nthC r cs))) → ElemModel.InvB M (ElemModel.G M)) →
             T (innFac S (just (l , r)) cs) → ElemModel.Inv3 M (ElemModel.ι M (ElemModel.F M) (ElemModel.G M))
innFac-sem {S} M l r cs readF readG p =
  ∨-elim (innerLaw S ∧ jinv (jdg (nthC l cs))) (rSplit S ∧ jinv (jdg (nthC r cs)))
    (λ q → Left.left-inv (ElemModel.sl M) (ElemModel.leftLaw M (fstT (innerLaw S) q))
              (ElemModel.F M) (ElemModel.G M) (readF (sndT (innerLaw S) q)))
    (λ q → Right.right-inv (ElemModel.sl M) (ElemModel.rightLaw M (fstT (rSplit S) q))
              (ElemModel.F M) (ElemModel.G M) (readG (sndT (rSplit S) q)))
    p

------------------------------------------------------------------------
-- Examples (notes §5.4): the directed Eckmann–Hilton cells inside an
-- object C. The head Σ(ΣD¹ ∨ ΣD¹) is an inner coherence (two-tier
-- reads it in the coherence case), with no Gray top generators; γ's
-- components are, in order, X, C, then the two inputs a, b. The
-- elementary interchanger's left input is component 2, right is 3.

private
  unm : Comp
  unm = comp (ip false false false) false
  invc : Comp
  invc = comp (ip true true true) false
  ordObj : Comp
  ordObj = comp (ip false false false) true

ehHead : Head
ehHead = head innerC [] false (just (2 , 3)) 1

-- unmarked, no switch: not invertible (directed); two-tier: invertible
eh-unmarked-V  : invU (setting false false) ehHead (unm ∷ unm ∷ unm ∷ unm ∷ []) ≡ false
eh-unmarked-V  = refl
eh-two-tier    : invT ehHead (unm ∷ unm ∷ unm ∷ unm ∷ []) ≡ true
eh-two-tier    = refl
-- C ord: invertible in every setting
eh-ord-V       : invU (setting false false) ehHead (unm ∷ ordObj ∷ unm ∷ unm ∷ []) ≡ true
eh-ord-V       = refl
-- a inv: invertible exactly when the left split is on
eh-inv-V       : invU (setting false false) ehHead (unm ∷ unm ∷ invc ∷ unm ∷ []) ≡ false
eh-inv-V       = refl
eh-inv-R       : invU (setting false true) ehHead (unm ∷ unm ∷ invc ∷ unm ∷ []) ≡ false
eh-inv-R       = refl
eh-inv-inner   : invU (setting true false) ehHead (unm ∷ unm ∷ invc ∷ unm ∷ []) ≡ true
eh-inv-inner   = refl
-- b inv: invertible exactly when R is on
eh-invb-inner  : invU (setting true false) ehHead (unm ∷ unm ∷ unm ∷ invc ∷ []) ≡ false
eh-invb-inner  = refl
eh-invb-R      : invU (setting false true) ehHead (unm ∷ unm ∷ unm ∷ invc ∷ []) ≡ true
eh-invb-R      = refl
