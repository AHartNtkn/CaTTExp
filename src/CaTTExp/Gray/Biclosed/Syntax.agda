------------------------------------------------------------------------
-- D7d: syntax of the Gray biclosed rules of the kernel
-- (notes/closed-structure.md F.7.4, from the verified r3 answer
-- notes/conjectures/answered/gray-biclosed-coherence-r3-2026-11-20.md,
-- Response 2).
--
-- Formulas (objects), multimap types (X₁, …, Xₙ ▸ Z), globular cell
-- types over a multimap type with a time-slot gap and a mode
-- (invertible / directed), and terms.  Boolean equality on all of
-- them, with soundness and reflexivity proofs.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Syntax where

open import CaTTExp.Prelude

-- Pasting shapes, kept abstract: globes, named shapes, and the Gray
-- tensor of contexts Δ ⊠ Θ.
data Shape : Set where
  disk  : Nat → Shape
  named : Nat → Shape
  _⊠_   : Shape → Shape → Shape

-- Formulas.  obj i is an object variable; rep Θ is the representable ⟦Θ⟧.
--   A \\ C  is  A\C = Hom_lax(A, C)
--   C // A  is  C/A = Hom_oplax(A, C)
data Fm : Set where
  obj  : Nat → Fm
  rep  : Shape → Fm
  _⊗_  : Fm → Fm → Fm
  _\\_ : Fm → Fm → Fm
  _//_ : Fm → Fm → Fm

-- Multimap types (X₁, …, Xₙ ▸ Z).
record MTy : Set where
  constructor _▸_
  field
    ins : List Fm
    out : Fm
open MTy public

data Mode : Set where
  inv dir : Mode

-- Rows of the cut rules (F.7.4 §2 table); their meaning is in Rows.agda.
data Row : Set where
  pairR  : List Fm → Fm → Fm → List Fm → Fm → Row        -- L U V R Z
  probeR : List Fm → Shape → Shape → List Fm → Fm → Row  -- L Δ Θ R Z
  unitR  : List Fm → List Fm → Fm → Row                  -- L R Z
  evLR   : List Fm → Fm → Fm → Row                       -- Φ A C
  evRR   : List Fm → Fm → Fm → Row                       -- Φ A C

-- A template: row, time-slot gap, mode and dimension.
record Tmpl : Set where
  constructor tmpl
  field
    row  : Row
    gap  : Nat
    mode : Mode
    dimn : Nat
open Tmpl public

-- The two goals of a template: the cell c and its comparison ε.
data Goal : Set where
  gc gε : Goal

mutual
  -- Terms.
  --   var i        context variable (de Bruijn level)
  --   mP U V       m_{U,V}   : (U, V ▸ U ⊗ V)
  --   eL A C       e^ℓ_{A,C} : (A, A\C ▸ C)
  --   eR A C       e^r_{A,C} : (C/A, A ▸ C)
  --   pP Δ Θ       p_{Δ,Θ}   : (⟦Δ⟧, ⟦Θ⟧ ▸ ⟦Δ ⊠ Θ⟧)
  --   pt           pt        : ( ▸ ⟦D⁰⟧)
  --   idt A        1_A       : (A ▸ A)
  --   comp f gs    planar substitution f ∘ (g₁, …, gₙ), whiskering when
  --                one argument is a higher cell
  --   glue a⁻ x a⁺ x with invertible collars adjoined on both sides
  --                (an L-core composite; its typing rule is in Typing)
  --   here t e φs ts  goal e of template t, instantiated by the
  --                substitution sending object variable i to φs[i] and
  --                context variable i to ts[i]
  data Tm : Set where
    var  : Nat → Tm
    mP   : Fm → Fm → Tm
    eL   : Fm → Fm → Tm
    eR   : Fm → Fm → Tm
    pP   : Shape → Shape → Tm
    pt   : Tm
    idt  : Fm → Tm
    comp : Tm → List Tm → Tm
    glue : Tm → Tm → Tm → Tm
    here : Tmpl → Goal → List Fm → List Tm → Tm

  -- Cell types.  op M: operations of type M.  hom m g T s t: cells from
  -- s to t (both of type T) with time slot at gap g, of mode m.
  data CTy : Set where
    op  : MTy → CTy
    hom : Mode → Nat → CTy → Tm → Tm → CTy

Ctx : Set
Ctx = List CTy

------------------------------------------------------------------------
-- Boolean equality

∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro {true} {true} _ _ = tt

eqSh : Shape → Shape → Bool
eqSh (disk m)  (disk n)  = m ==ℕ n
eqSh (named m) (named n) = m ==ℕ n
eqSh (a ⊠ b)   (c ⊠ d)   = eqSh a c ∧ eqSh b d
eqSh _ _ = false

eqFm : Fm → Fm → Bool
eqFm (obj m)  (obj n)  = m ==ℕ n
eqFm (rep a)  (rep b)  = eqSh a b
eqFm (a ⊗ b)  (c ⊗ d)  = eqFm a c ∧ eqFm b d
eqFm (a \\ b) (c \\ d) = eqFm a c ∧ eqFm b d
eqFm (a // b) (c // d) = eqFm a c ∧ eqFm b d
eqFm _ _ = false

eqFms : List Fm → List Fm → Bool
eqFms []       []       = true
eqFms (a ∷ as) (b ∷ bs) = eqFm a b ∧ eqFms as bs
eqFms _ _ = false

eqMTy : MTy → MTy → Bool
eqMTy (xs ▸ z) (ys ▸ w) = eqFms xs ys ∧ eqFm z w

eqMode : Mode → Mode → Bool
eqMode inv inv = true
eqMode dir dir = true
eqMode _ _ = false

eqRow : Row → Row → Bool
eqRow (pairR a b c d e)  (pairR a′ b′ c′ d′ e′)  =
  eqFms a a′ ∧ eqFm b b′ ∧ eqFm c c′ ∧ eqFms d d′ ∧ eqFm e e′
eqRow (probeR a b c d e) (probeR a′ b′ c′ d′ e′) =
  eqFms a a′ ∧ eqSh b b′ ∧ eqSh c c′ ∧ eqFms d d′ ∧ eqFm e e′
eqRow (unitR a b c)      (unitR a′ b′ c′)        = eqFms a a′ ∧ eqFms b b′ ∧ eqFm c c′
eqRow (evLR a b c)       (evLR a′ b′ c′)         = eqFms a a′ ∧ eqFm b b′ ∧ eqFm c c′
eqRow (evRR a b c)       (evRR a′ b′ c′)         = eqFms a a′ ∧ eqFm b b′ ∧ eqFm c c′
eqRow _ _ = false

eqTmpl : Tmpl → Tmpl → Bool
eqTmpl (tmpl r g m n) (tmpl r′ g′ m′ n′) =
  eqRow r r′ ∧ (g ==ℕ g′) ∧ eqMode m m′ ∧ (n ==ℕ n′)

eqGoal : Goal → Goal → Bool
eqGoal gc gc = true
eqGoal gε gε = true
eqGoal _  _  = false

mutual
  eqTm : Tm → Tm → Bool
  eqTm (var m)      (var n)      = m ==ℕ n
  eqTm (mP a b)     (mP c d)     = eqFm a c ∧ eqFm b d
  eqTm (eL a b)     (eL c d)     = eqFm a c ∧ eqFm b d
  eqTm (eR a b)     (eR c d)     = eqFm a c ∧ eqFm b d
  eqTm (pP a b)     (pP c d)     = eqSh a c ∧ eqSh b d
  eqTm pt           pt           = true
  eqTm (idt a)      (idt b)      = eqFm a b
  eqTm (comp f gs)  (comp h ks)  = eqTm f h ∧ eqTms gs ks
  eqTm (glue a x b) (glue c y d) = eqTm a c ∧ eqTm x y ∧ eqTm b d
  eqTm (here t e φs ts) (here t′ e′ φs′ ts′) =
    eqTmpl t t′ ∧ eqGoal e e′ ∧ eqFms φs φs′ ∧ eqTms ts ts′
  eqTm _ _ = false

  eqTms : List Tm → List Tm → Bool
  eqTms []       []       = true
  eqTms (a ∷ as) (b ∷ bs) = eqTm a b ∧ eqTms as bs
  eqTms _ _ = false

  eqTy : CTy → CTy → Bool
  eqTy (op M)          (op N)          = eqMTy M N
  eqTy (hom m g A s t) (hom n h B u v) =
    eqMode m n ∧ (g ==ℕ h) ∧ eqTy A B ∧ eqTm s u ∧ eqTm t v
  eqTy _ _ = false

eqCtx : Ctx → Ctx → Bool
eqCtx []       []       = true
eqCtx (a ∷ as) (b ∷ bs) = eqTy a b ∧ eqCtx as bs
eqCtx _ _ = false

------------------------------------------------------------------------
-- Soundness

eqSh-sound : ∀ a b → T (eqSh a b) → a ≡ b
eqSh-sound (disk m)  (disk n)  p = cong disk (==ℕ-sound m n p)
eqSh-sound (named m) (named n) p = cong named (==ℕ-sound m n p)
eqSh-sound (a ⊠ b)   (c ⊠ d)   p =
  cong₂ _⊠_ (eqSh-sound a c (∧-fst p)) (eqSh-sound b d (∧-snd {eqSh a c} p))

eqFm-sound : ∀ a b → T (eqFm a b) → a ≡ b
eqFm-sound (obj m)  (obj n)  p = cong obj (==ℕ-sound m n p)
eqFm-sound (rep a)  (rep b)  p = cong rep (eqSh-sound a b p)
eqFm-sound (a ⊗ b)  (c ⊗ d)  p =
  cong₂ _⊗_ (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))
eqFm-sound (a \\ b) (c \\ d) p =
  cong₂ _\\_ (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))
eqFm-sound (a // b) (c // d) p =
  cong₂ _//_ (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))

eqFms-sound : ∀ a b → T (eqFms a b) → a ≡ b
eqFms-sound []       []       _ = refl
eqFms-sound (a ∷ as) (b ∷ bs) p =
  cong₂ _∷_ (eqFm-sound a b (∧-fst p)) (eqFms-sound as bs (∧-snd {eqFm a b} p))

eqMTy-sound : ∀ a b → T (eqMTy a b) → a ≡ b
eqMTy-sound (xs ▸ z) (ys ▸ w) p =
  cong₂ _▸_ (eqFms-sound xs ys (∧-fst p)) (eqFm-sound z w (∧-snd {eqFms xs ys} p))

eqMode-sound : ∀ a b → T (eqMode a b) → a ≡ b
eqMode-sound inv inv _ = refl
eqMode-sound dir dir _ = refl

eqGoal-sound : ∀ a b → T (eqGoal a b) → a ≡ b
eqGoal-sound gc gc _ = refl
eqGoal-sound gε gε _ = refl

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  cong₅ : ∀ {A B C D E F : Set} (f : A → B → C → D → E → F)
          {a a' b b' c c' d d' e e'} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' →
          f a b c d e ≡ f a' b' c' d' e'
  cong₅ f refl refl refl refl refl = refl

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a' b b' c c' d d'} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
  cong₄ f refl refl refl refl = refl

-- split a proof of a right-nested conjunction
∧₅ : ∀ {a b c d e} → T (a ∧ b ∧ c ∧ d ∧ e) → T a × T b × T c × T d × T e
∧₅ {true} {true} {true} {true} {true} _ = tt , tt , tt , tt , tt

∧₃ : ∀ {a b c} → T (a ∧ b ∧ c) → T a × T b × T c
∧₃ {true} {true} {true} _ = tt , tt , tt

∧₄ : ∀ {a b c d} → T (a ∧ b ∧ c ∧ d) → T a × T b × T c × T d
∧₄ {true} {true} {true} {true} _ = tt , tt , tt , tt

eqRow-sound : ∀ a b → T (eqRow a b) → a ≡ b
eqRow-sound (pairR a b c d e) (pairR a′ b′ c′ d′ e′) p =
  let (p1 , p2 , p3 , p4 , p5) = ∧₅ {eqFms a a′} p in
  cong₅ pairR (eqFms-sound a a′ p1) (eqFm-sound b b′ p2) (eqFm-sound c c′ p3)
              (eqFms-sound d d′ p4) (eqFm-sound e e′ p5)
eqRow-sound (probeR a b c d e) (probeR a′ b′ c′ d′ e′) p =
  let (p1 , p2 , p3 , p4 , p5) = ∧₅ {eqFms a a′} p in
  cong₅ probeR (eqFms-sound a a′ p1) (eqSh-sound b b′ p2) (eqSh-sound c c′ p3)
               (eqFms-sound d d′ p4) (eqFm-sound e e′ p5)
eqRow-sound (unitR a b c) (unitR a′ b′ c′) p =
  let (p1 , p2 , p3) = ∧₃ {eqFms a a′} p in
  cong₃ unitR (eqFms-sound a a′ p1) (eqFms-sound b b′ p2) (eqFm-sound c c′ p3)
eqRow-sound (evLR a b c) (evLR a′ b′ c′) p =
  let (p1 , p2 , p3) = ∧₃ {eqFms a a′} p in
  cong₃ evLR (eqFms-sound a a′ p1) (eqFm-sound b b′ p2) (eqFm-sound c c′ p3)
eqRow-sound (evRR a b c) (evRR a′ b′ c′) p =
  let (p1 , p2 , p3) = ∧₃ {eqFms a a′} p in
  cong₃ evRR (eqFms-sound a a′ p1) (eqFm-sound b b′ p2) (eqFm-sound c c′ p3)

eqTmpl-sound : ∀ a b → T (eqTmpl a b) → a ≡ b
eqTmpl-sound (tmpl r g m n) (tmpl r′ g′ m′ n′) p =
  let (p1 , p2 , p3 , p4) = ∧₄ {eqRow r r′} p in
  cong₄ tmpl (eqRow-sound r r′ p1) (==ℕ-sound g g′ p2) (eqMode-sound m m′ p3) (==ℕ-sound n n′ p4)

mutual
  eqTm-sound : ∀ a b → T (eqTm a b) → a ≡ b
  eqTm-sound (var m)  (var n)  p = cong var (==ℕ-sound m n p)
  eqTm-sound (mP a b) (mP c d) p =
    cong₂ mP (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))
  eqTm-sound (eL a b) (eL c d) p =
    cong₂ eL (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))
  eqTm-sound (eR a b) (eR c d) p =
    cong₂ eR (eqFm-sound a c (∧-fst p)) (eqFm-sound b d (∧-snd {eqFm a c} p))
  eqTm-sound (pP a b) (pP c d) p =
    cong₂ pP (eqSh-sound a c (∧-fst p)) (eqSh-sound b d (∧-snd {eqSh a c} p))
  eqTm-sound pt pt _ = refl
  eqTm-sound (idt a) (idt b) p = cong idt (eqFm-sound a b p)
  eqTm-sound (comp f gs) (comp h ks) p =
    cong₂ comp (eqTm-sound f h (∧-fst p)) (eqTms-sound gs ks (∧-snd {eqTm f h} p))
  eqTm-sound (glue a x b) (glue c y d) p =
    let q = ∧-snd {eqTm a c} p in
    cong₃ glue (eqTm-sound a c (∧-fst p)) (eqTm-sound x y (∧-fst q))
               (eqTm-sound b d (∧-snd {eqTm x y} q))
  eqTm-sound (here t e φs ts) (here t′ e′ φs′ ts′) p =
    let (p1 , p2 , p3 , p4) = ∧₄ {eqTmpl t t′} p in
    cong₄ here (eqTmpl-sound t t′ p1) (eqGoal-sound e e′ p2)
               (eqFms-sound φs φs′ p3) (eqTms-sound ts ts′ p4)

  eqTms-sound : ∀ a b → T (eqTms a b) → a ≡ b
  eqTms-sound []       []       _ = refl
  eqTms-sound (a ∷ as) (b ∷ bs) p =
    cong₂ _∷_ (eqTm-sound a b (∧-fst p)) (eqTms-sound as bs (∧-snd {eqTm a b} p))

  eqTy-sound : ∀ a b → T (eqTy a b) → a ≡ b
  eqTy-sound (op M) (op N) p = cong op (eqMTy-sound M N p)
  eqTy-sound (hom m g A s t) (hom n h B u v) p =
    let p1 = ∧-snd {eqMode m n} p
        p2 = ∧-snd {g ==ℕ h} p1
        p3 = ∧-snd {eqTy A B} p2
    in cong₅ hom (eqMode-sound m n (∧-fst p)) (==ℕ-sound g h (∧-fst p1))
                 (eqTy-sound A B (∧-fst p2)) (eqTm-sound s u (∧-fst p3))
                 (eqTm-sound t v (∧-snd {eqTm s u} p3))

eqCtx-sound : ∀ a b → T (eqCtx a b) → a ≡ b
eqCtx-sound []       []       _ = refl
eqCtx-sound (a ∷ as) (b ∷ bs) p =
  cong₂ _∷_ (eqTy-sound a b (∧-fst p)) (eqCtx-sound as bs (∧-snd {eqTy a b} p))

------------------------------------------------------------------------
-- Reflexivity

eqSh-refl : ∀ a → T (eqSh a a)
eqSh-refl (disk n)  = ==ℕ-refl n
eqSh-refl (named n) = ==ℕ-refl n
eqSh-refl (a ⊠ b)   = ∧-intro (eqSh-refl a) (eqSh-refl b)

eqFm-refl : ∀ a → T (eqFm a a)
eqFm-refl (obj n)  = ==ℕ-refl n
eqFm-refl (rep a)  = eqSh-refl a
eqFm-refl (a ⊗ b)  = ∧-intro (eqFm-refl a) (eqFm-refl b)
eqFm-refl (a \\ b) = ∧-intro (eqFm-refl a) (eqFm-refl b)
eqFm-refl (a // b) = ∧-intro (eqFm-refl a) (eqFm-refl b)

eqFms-refl : ∀ a → T (eqFms a a)
eqFms-refl []       = tt
eqFms-refl (a ∷ as) = ∧-intro (eqFm-refl a) (eqFms-refl as)

eqMTy-refl : ∀ a → T (eqMTy a a)
eqMTy-refl (xs ▸ z) = ∧-intro (eqFms-refl xs) (eqFm-refl z)

eqMode-refl : ∀ a → T (eqMode a a)
eqMode-refl inv = tt
eqMode-refl dir = tt

eqGoal-refl : ∀ a → T (eqGoal a a)
eqGoal-refl gc = tt
eqGoal-refl gε = tt

eqRow-refl : ∀ a → T (eqRow a a)
eqRow-refl (pairR a b c d e)  = ∧-intro (eqFms-refl a) (∧-intro (eqFm-refl b) (∧-intro (eqFm-refl c) (∧-intro (eqFms-refl d) (eqFm-refl e))))
eqRow-refl (probeR a b c d e) = ∧-intro (eqFms-refl a) (∧-intro (eqSh-refl b) (∧-intro (eqSh-refl c) (∧-intro (eqFms-refl d) (eqFm-refl e))))
eqRow-refl (unitR a b c)      = ∧-intro (eqFms-refl a) (∧-intro (eqFms-refl b) (eqFm-refl c))
eqRow-refl (evLR a b c)       = ∧-intro (eqFms-refl a) (∧-intro (eqFm-refl b) (eqFm-refl c))
eqRow-refl (evRR a b c)       = ∧-intro (eqFms-refl a) (∧-intro (eqFm-refl b) (eqFm-refl c))

eqTmpl-refl : ∀ a → T (eqTmpl a a)
eqTmpl-refl (tmpl r g m n) =
  ∧-intro (eqRow-refl r) (∧-intro (==ℕ-refl g) (∧-intro (eqMode-refl m) (==ℕ-refl n)))

mutual
  eqTm-refl : ∀ a → T (eqTm a a)
  eqTm-refl (var n)      = ==ℕ-refl n
  eqTm-refl (mP a b)     = ∧-intro (eqFm-refl a) (eqFm-refl b)
  eqTm-refl (eL a b)     = ∧-intro (eqFm-refl a) (eqFm-refl b)
  eqTm-refl (eR a b)     = ∧-intro (eqFm-refl a) (eqFm-refl b)
  eqTm-refl (pP a b)     = ∧-intro (eqSh-refl a) (eqSh-refl b)
  eqTm-refl pt           = tt
  eqTm-refl (idt a)      = eqFm-refl a
  eqTm-refl (comp f gs)  = ∧-intro (eqTm-refl f) (eqTms-refl gs)
  eqTm-refl (glue a x b) = ∧-intro (eqTm-refl a) (∧-intro (eqTm-refl x) (eqTm-refl b))
  eqTm-refl (here t e φs ts) =
    ∧-intro (eqTmpl-refl t) (∧-intro (eqGoal-refl e) (∧-intro (eqFms-refl φs) (eqTms-refl ts)))

  eqTms-refl : ∀ a → T (eqTms a a)
  eqTms-refl []       = tt
  eqTms-refl (a ∷ as) = ∧-intro (eqTm-refl a) (eqTms-refl as)

  eqTy-refl : ∀ a → T (eqTy a a)
  eqTy-refl (op M) = eqMTy-refl M
  eqTy-refl (hom m g A s t) =
    ∧-intro (eqMode-refl m) (∧-intro (==ℕ-refl g)
      (∧-intro (eqTy-refl A) (∧-intro (eqTm-refl s) (eqTm-refl t))))

eqCtx-refl : ∀ a → T (eqCtx a a)
eqCtx-refl []       = tt
eqCtx-refl (a ∷ as) = ∧-intro (eqTy-refl a) (eqCtx-refl as)
