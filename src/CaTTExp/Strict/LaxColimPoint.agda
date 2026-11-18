------------------------------------------------------------------------
-- Ledger C8(4): the lax colimit of the point, in the strict model.
--
-- Let Γ be a globular presentation: generators a of dimension dim a,
-- with a source s a and a target t a of dimension dim a − 1 when
-- dim a ≥ 1. Its Steiner complex λΓ has basis the generators and
--     ∂⁻ a = s a,  ∂⁺ a = t a          (dim a ≥ 1).
--
-- A lax cocone over a Γ-diagram with vertex c is a map Γ ⊗ D¹ → X
-- (conventions.md §3.1, AM Remark 1.13, Loubaton Def. of lax
-- transformation). Over the constant diagram at 1 it sends the 0-end
-- Γ ⊗ {0} to (identities on) 1 and the 1-end Γ ⊗ {1} to (identities
-- on) c. So lax cocones from const 1 to c are maps out of the quotient
-- of Γ ⊗ D¹ that collapses each end to a point.
--
-- At the level of Steiner complexes, with the Leibniz rule of
-- conventions.md §2,
--     ∂^α(x ⊗ y) = (∂^α x ⊗ y) ∪ (x ⊗ ∂^{(−1)^{dim x} α} y),
-- this module computes that quotient for every Γ:
--
--   `lax`    The collapse q : λΓ ⊗ λD¹ → Σ λΓ, with
--                q(x ⊗ 0) = ⊥,  q(x ⊗ 1) = ⊤      (dim x = 0)
--                q(b ⊗ 0) = q(b ⊗ 1) = 0           (dim b ≥ 1)
--                q(a ⊗ i) = Σa                     (i : 0 → 1)
--            preserves the positive and the negative boundary of every
--            basis element it does not kill, and identifies the two
--            boundaries of every basis element it kills. So it is a
--            map of augmented directed complexes, and the cocone cell
--            of a runs from the cocone cell of ∂⁻a to that of ∂⁺a, in
--            every dimension: the quotient is the suspension Σ_{⊥,⊤}Γ
--            with NO dual. Hence laxcolim(const 1) ≅ Free(Γ).
--   `oplax`  The same collapse of D¹ ⊗ Γ (oplax cocones) lands in the
--            suspension of the total dual Γ°: the cell of a runs from
--            the cell of ∂⁺a to that of ∂⁻a for every a of dimension
--            ≥ 1.
--   `q-onto`, `q-bot`, `q-top`, `q-kill`, `q-inj`: q kills exactly
--            the end cells of positive dimension, sends the objects of
--            each end to one point, and is a bijection from the cells
--            a ⊗ i onto the cells Σa.
--
-- This agrees with Loubaton (arXiv 2406.05425, Ex. 4.2.3.12),
-- laxcolim_{A♭} 1 ≃ A, and with the paper computation of
-- free-objects-proofs.md §6a. The examples at the end instantiate it
-- for D¹, D², the loop and the composable pair. The passage from
-- complexes to strict ω-categories (ν(λΓ ⊗ λD¹) ≅ ν(λΓ) ⊗ D¹, and
-- ν(λΓ) = Free(Γ) for loop-free Γ) is cited, not formalised; see
-- notes/free-objects-proofs.md §6a.
------------------------------------------------------------------------
module CaTTExp.Strict.LaxColimPoint where

open import CaTTExp.Prelude

record Glob : Set where
  field
    gdim : Nat → Nat
    s t  : Nat → Nat
    -- Only boundaries one dimension down; globularity of the
    -- presentation is not needed for the computation.
    wf   : ∀ a k → gdim a ≡ suc k → (gdim (s a) ≡ k) × (gdim (t a) ≡ k)

module _ (Γ : Glob) where
  open Glob Γ

  sel : Bool → Nat → Nat
  sel α a = if α then t a else s a

  sel-dim : ∀ α a k → gdim a ≡ suc k → gdim (sel α a) ≡ k
  sel-dim true  a k e = snd (wf a k e)
  sel-dim false a k e = fst (wf a k e)

  ----------------------------------------------------------------------
  -- λΓ, λD¹ and the Leibniz rule.

  bdL : Nat → Bool → Nat → List Nat
  bdL zero    α a = []
  bdL (suc _) α a = sel α a ∷ []

  ∂L : Bool → Nat → List Nat
  ∂L α a = bdL (gdim a) α a

  data D1 : Set where
    d0 d1 de : D1          -- the objects 0, 1 and the arrow i : 0 → 1

  ∂D : Bool → D1 → List D1
  ∂D α de = (if α then d1 else d0) ∷ []
  ∂D α d0 = []
  ∂D α d1 = []

  even : Nat → Bool
  even zero          = true
  even (suc zero)    = false
  even (suc (suc n)) = even n

  -- (−1)^k α
  sg : Nat → Bool → Bool
  sg k α = if even k then α else not α

  map : ∀ {A B : Set} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- Γ ⊗ D¹ (lax), basis a ⊗ i.
  record TB : Set where
    constructor _⊗_
    field gen : Nat
          end : D1

  ∂T : Bool → TB → List TB
  ∂T α (a ⊗ i) = map (λ b → b ⊗ i) (∂L α a) ++ map (λ j → a ⊗ j) (∂D (sg (gdim a) α) i)

  -- D¹ ⊗ Γ (oplax), basis i ⊙ a; dim i is 1 for i = de, else 0.
  record OB : Set where
    constructor _⊙_
    field end : D1
          gen : Nat

  dimD : D1 → Nat
  dimD de = 1
  dimD _  = 0

  ∂O : Bool → OB → List OB
  ∂O α (i ⊙ a) = map (λ j → j ⊙ a) (∂D α i) ++ map (λ b → i ⊙ b) (∂L (sg (dimD i) α) a)

  ----------------------------------------------------------------------
  -- The suspension Σ_{⊥,⊤} λΓ, and its total dual.

  data SB : Set where
    bot top : SB
    sus     : Nat → SB

  bdS : Nat → Bool → Nat → List SB
  bdS zero    α a = (if α then top else bot) ∷ []
  bdS (suc _) α a = sus (sel α a) ∷ []

  ∂S : Bool → SB → List SB
  ∂S α (sus a) = bdS (gdim a) α a
  ∂S α _       = []

  -- Σ(Γ°): every cell of Γ of dimension ≥ 1 reversed.
  bdS° : Nat → Bool → Nat → List SB
  bdS° zero    α a = (if α then top else bot) ∷ []
  bdS° (suc _) α a = sus (sel (not α) a) ∷ []

  ∂S° : Bool → SB → List SB
  ∂S° α (sus a) = bdS° (gdim a) α a
  ∂S° α _       = []

  ----------------------------------------------------------------------
  -- The collapse of both ends.

  qz : Nat → SB → Maybe SB
  qz zero    x = just x
  qz (suc _) x = nothing

  q : TB → Maybe SB
  q (a ⊗ d0) = qz (gdim a) bot
  q (a ⊗ d1) = qz (gdim a) top
  q (a ⊗ de) = just (sus a)

  qo : OB → Maybe SB
  qo (d0 ⊙ a) = qz (gdim a) bot
  qo (d1 ⊙ a) = qz (gdim a) top
  qo (de ⊙ a) = just (sus a)

  -- Linear extension (killed elements go to 0).
  ext : ∀ {B : Set} → (B → Maybe SB) → List B → List SB
  ext f []       = []
  ext f (x ∷ xs) with f x
  ... | just y  = y ∷ ext f xs
  ... | nothing = ext f xs

  -- What a map of augmented directed complexes needs of a basis
  -- element β: if β ↦ γ, the boundaries of β go to those of γ; if
  -- β ↦ 0, its two boundaries go to the same chain.
  Pres : (Bool → SB → List SB) → Maybe SB → List SB → List SB → Set
  Pres ∂ (just γ) P N = (P ≡ ∂ true γ) × (N ≡ ∂ false γ)
  Pres ∂ nothing  P N = P ≡ N

  ----------------------------------------------------------------------
  -- Theorems.

  private
    qz-0 : ∀ a x → gdim a ≡ 0 → qz (gdim a) x ≡ just x
    qz-0 a x e rewrite e = refl

    qz-s : ∀ a x k → gdim a ≡ suc k → qz (gdim a) x ≡ nothing
    qz-s a x k e rewrite e = refl


  lax : ∀ β → Pres ∂S (q β) (ext q (∂T true β)) (ext q (∂T false β))
  lax (a ⊗ d0) with gdim a in e
  ... | zero  = refl , refl
  ... | suc zero rewrite qz-0 (s a) bot (fst (wf a 0 e)) | qz-0 (t a) bot (snd (wf a 0 e)) = refl
  ... | suc (suc k) rewrite qz-s (s a) bot k (fst (wf a (suc k) e)) | qz-s (t a) bot k (snd (wf a (suc k) e)) = refl
  lax (a ⊗ d1) with gdim a in e
  ... | zero  = refl , refl
  ... | suc zero rewrite qz-0 (s a) top (fst (wf a 0 e)) | qz-0 (t a) top (snd (wf a 0 e)) = refl
  ... | suc (suc k) rewrite qz-s (s a) top k (fst (wf a (suc k) e)) | qz-s (t a) top k (snd (wf a (suc k) e)) = refl
  lax (a ⊗ de) with gdim a in e
  ... | zero  rewrite e = refl , refl
  ... | suc k with even (suc k)
  ...   | true  rewrite e = refl , refl
  ...   | false rewrite e = refl , refl

  oplax : ∀ β → Pres ∂S° (qo β) (ext qo (∂O true β)) (ext qo (∂O false β))
  oplax (d0 ⊙ a) with gdim a in e
  ... | zero  = refl , refl
  ... | suc zero rewrite qz-0 (s a) bot (fst (wf a 0 e)) | qz-0 (t a) bot (snd (wf a 0 e)) = refl
  ... | suc (suc k) rewrite qz-s (s a) bot k (fst (wf a (suc k) e)) | qz-s (t a) bot k (snd (wf a (suc k) e)) = refl
  oplax (d1 ⊙ a) with gdim a in e
  ... | zero  = refl , refl
  ... | suc zero rewrite qz-0 (s a) top (fst (wf a 0 e)) | qz-0 (t a) top (snd (wf a 0 e)) = refl
  ... | suc (suc k) rewrite qz-s (s a) top k (fst (wf a (suc k) e)) | qz-s (t a) top k (snd (wf a (suc k) e)) = refl
  oplax (de ⊙ a) with gdim a in e
  ... | zero  = refl , refl
  ... | suc k = refl , refl

  -- q kills exactly the end cells of positive dimension, sends the
  -- objects of each end to one point, and is otherwise injective and
  -- onto.
  q-onto : ∀ a → q (a ⊗ de) ≡ just (sus a)
  q-onto a = refl

  q-bot : ∀ x → gdim x ≡ 0 → q (x ⊗ d0) ≡ just bot
  q-bot x e = qz-0 x bot e

  q-top : ∀ x → gdim x ≡ 0 → q (x ⊗ d1) ≡ just top
  q-top x e = qz-0 x top e

  q-kill : ∀ b k → gdim b ≡ suc k → (q (b ⊗ d0) ≡ nothing) × (q (b ⊗ d1) ≡ nothing)
  q-kill b k e = qz-s b bot k e , qz-s b top k e

  q-inj : ∀ β β′ a → q β ≡ just (sus a) → q β′ ≡ just (sus a) → β ≡ β′
  q-inj (b ⊗ de) (b′ ⊗ de) a refl refl = refl
  q-inj (b ⊗ d0) β′ a p q′ with gdim b
  q-inj (b ⊗ d0) β′ a () q′ | zero
  q-inj (b ⊗ d0) β′ a () q′ | suc _
  q-inj (b ⊗ d1) β′ a p q′ with gdim b
  q-inj (b ⊗ d1) β′ a () q′ | zero
  q-inj (b ⊗ d1) β′ a () q′ | suc _
  q-inj (b ⊗ de) (b′ ⊗ d0) a p q′ with gdim b′
  q-inj (b ⊗ de) (b′ ⊗ d0) a p () | zero
  q-inj (b ⊗ de) (b′ ⊗ d0) a p () | suc _
  q-inj (b ⊗ de) (b′ ⊗ d1) a p q′ with gdim b′
  q-inj (b ⊗ de) (b′ ⊗ d1) a p () | zero
  q-inj (b ⊗ de) (b′ ⊗ d1) a p () | suc _

------------------------------------------------------------------------
-- Examples: D¹, D², the loop and the composable pair. Generators past
-- the last are objects (unused). In each, the cocone cell of a
-- positive-dimensional generator runs from the cell of its source to
-- the cell of its target (lax), and the other way round (oplax).

-- D¹:  x0  y1  f2 : x → y
D¹ : Glob
D¹ = record { gdim = d ; s = λ _ → 0 ; t = λ _ → 1 ; wf = w }
  where
  d : Nat → Nat
  d 2 = 1
  d _ = 0
  w : ∀ a k → d a ≡ suc k → (d 0 ≡ k) × (d 1 ≡ k)
  w 2 zero refl = refl , refl

-- D²:  x0  y1  f2 g3 : x → y  α4 : f ⇒ g
D² : Glob
D² = record { gdim = d ; s = sD ; t = tD ; wf = w }
  where
  d : Nat → Nat
  d 2 = 1
  d 3 = 1
  d 4 = 2
  d _ = 0
  sD tD : Nat → Nat
  sD 4 = 2
  sD _ = 0
  tD 4 = 3
  tD _ = 1
  w : ∀ a k → d a ≡ suc k → (d (sD a) ≡ k) × (d (tD a) ≡ k)
  w 2 zero    refl = refl , refl
  w 3 zero    refl = refl , refl
  w 4 (suc zero) refl = refl , refl

-- The loop:  x0  ℓ1 : x → x
Loop : Glob
Loop = record { gdim = d ; s = λ _ → 0 ; t = λ _ → 0 ; wf = w }
  where
  d : Nat → Nat
  d 1 = 1
  d _ = 0
  w : ∀ a k → d a ≡ suc k → (d 0 ≡ k) × (d 0 ≡ k)
  w 1 zero refl = refl , refl

-- The composable pair:  x0  y1  z2  f3 : x → y  g4 : y → z
Pair : Glob
Pair = record { gdim = d ; s = sP ; t = tP ; wf = w }
  where
  d : Nat → Nat
  d 3 = 1
  d 4 = 1
  d _ = 0
  sP tP : Nat → Nat
  sP 4 = 1
  sP _ = 0
  tP 4 = 2
  tP _ = 1
  w : ∀ a k → d a ≡ suc k → (d (sP a) ≡ k) × (d (tP a) ≡ k)
  w 3 zero refl = refl , refl
  w 4 zero refl = refl , refl

-- D¹: the cocone cell of f runs q_x → q_y; q_x runs ⊥ → ⊤.
_ : ext D¹ (q D¹) (∂T D¹ false (_⊗_ 2 de)) ≡ sus 0 ∷ []
_ = refl
_ : ext D¹ (q D¹) (∂T D¹ true (_⊗_ 2 de)) ≡ sus 1 ∷ []
_ = refl
_ : ext D¹ (q D¹) (∂T D¹ false (_⊗_ 0 de)) ≡ bot ∷ []
_ = refl
_ : ext D¹ (q D¹) (∂T D¹ true (_⊗_ 0 de)) ≡ top ∷ []
_ = refl

-- D²: the cell of α runs q_f ⇒ q_g (lax), q_g ⇒ q_f (oplax).
_ : ext D² (q D²) (∂T D² false (_⊗_ 4 de)) ≡ sus 2 ∷ []
_ = refl
_ : ext D² (q D²) (∂T D² true (_⊗_ 4 de)) ≡ sus 3 ∷ []
_ = refl
_ : ext D² (qo D²) (∂O D² false (_⊙_ de 4)) ≡ sus 3 ∷ []
_ = refl
_ : ext D² (qo D²) (∂O D² true (_⊙_ de 4)) ≡ sus 2 ∷ []
_ = refl
-- the end cell α ⊗ 0 is killed, and its boundaries agree after q
_ : q D² (_⊗_ 4 d0) ≡ nothing
_ = refl

-- The loop: the cell of ℓ is a loop on q_x.
_ : ext Loop (q Loop) (∂T Loop false (_⊗_ 1 de)) ≡ sus 0 ∷ []
_ = refl
_ : ext Loop (q Loop) (∂T Loop true (_⊗_ 1 de)) ≡ sus 0 ∷ []
_ = refl

-- The composable pair: q_f : q_x → q_y and q_g : q_y → q_z.
_ : ext Pair (q Pair) (∂T Pair true (_⊗_ 3 de)) ≡ sus 1 ∷ []
_ = refl
_ : ext Pair (q Pair) (∂T Pair false (_⊗_ 4 de)) ≡ sus 1 ∷ []
_ = refl
_ : ext Pair (q Pair) (∂T Pair true (_⊗_ 4 de)) ≡ sus 2 ∷ []
_ = refl
