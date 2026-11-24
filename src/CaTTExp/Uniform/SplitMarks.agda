------------------------------------------------------------------------
-- Split marks: the two crossing laws as object marks in the context
-- (ledger S31; notes/design-decisions.md §1.8; spec §2.3, §3.6).
--
-- Until 2026-11-24 the inner composite-crossing law (left split) and
-- the right split R were file-level switches: a development declared a
-- setting S ⊆ {inner law, R} once, and every coherence was checked in
-- V + S. S31 replaces that global, out-of-context assumption by two
-- object marks, as for `iord` and `ord`:
--
--   (C : ⋆)^lsplit   every inner crossing in a hom 𝒦(X, C) satisfies
--                    the left split (the inner law);
--   (C : ⋆)^rsplit   the same for the right split R;
--   `ord` implies both (inner letters into C are trivial, and both
--   sides of each law are pure inner terms: law-inner below).
--
-- A head over a pasting context Γ with objects a₀ … aₙ computes its
-- side condition in V + S(Γ), where S(Γ) is the meet of the laws carried
-- by a₁ … aₙ (a₀ is the target of no hom, so its marks are irrelevant,
-- as for (COH-ord)); a head whose objects are all `ord` still uses
-- (COH-ord).
--
-- This module proves, on the rule data of CaTTExp.Uniform.MarksRepaired:
--   * for a head with at least one hom, marking every object a₁ … aₙ
--     with laws S (and none `ord`, unless S is both) gives S(Γ) = S,
--     the old file setting; the judgments then agree by congruence
--                                                   (uniform-recovers)
--   * every object of the head carries every law of S(Γ), the step the
--     soundness argument uses                        (meet-lb)
--   * stronger marks give a larger setting, hence more judgments
--     (pointwise mark order; substitution itself is not modelled)
--                                                   (meet-mono, invM-mono)
--   * `ord` carries both laws, by definition of `laws`; justified by
--     law-trivial below plus the paper parallelism step (ord-both)
--   * directed Eckmann–Hilton (spec §3.6 Example (a)): with C marked
--     lsplit and a inv, or rsplit and b inv, (INN-fac) applies;
--     unmarked, or with the split on the wrong side, it does not; the
--     marks of a₀ are ignored         (eh-lsplit, eh-rsplit, eh-none,
--                                       eh-*-wrong-side)
--   * at degree 4, both sides of every split law are built from inner
--     interchangers, identities and whiskerings only, so any predicate
--     closed under those constructors (for example "is an identity" in
--     a model with trivial inner letters) holds of both sides
--                                                   (law-trivial)
-- Not mechanized: that `str` in the split marks agrees with `om` in the
-- components; any link between Degree4's laws (indexed by Switches)
-- and the marks; that the two sides of a law are parallel (by the
-- typing of T, by inspection), so that two identities are equal; the
-- factorization of a model's map through F_{V+S(Γ)}(Γ) (paper, design-
-- decisions.md §1.8); laws in degrees above 4 (paper).
------------------------------------------------------------------------
module CaTTExp.Uniform.SplitMarks where

open import CaTTExp.Prelude
open import CaTTExp.Pure using (∅)
open import CaTTExp.Gray.Marks ∅ using (ip)
open import CaTTExp.Uniform.Marks
  using (Setting; setting; innerLaw; rSplit; _≤S_; innerC)
open import CaTTExp.Uniform.MarksRepaired
  using (OMark; noM; iordM; ordM; isO; Comp; comp; om; Head; head;
         invU; setting-mono′)
import CaTTExp.Join.SwitchLaws as SL

------------------------------------------------------------------------
-- Object marks with the split bits.

record SMark : Set where
  constructor smark
  field
    lsp : Bool      -- lsplit: the inner law (left split)
    rsp : Bool      -- rsplit: R (right split)
    str : OMark     -- noM, iordM or ordM
open SMark public

-- The laws an object carries. `ord` carries both.
laws : SMark → Setting
laws m = if isO (str m) then setting true true else setting (lsp m) (rsp m)

ord-both : ∀ l r → laws (smark l r ordM) ≡ setting true true
ord-both l r = refl

_∧S_ : Setting → Setting → Setting
S ∧S S′ = setting (innerLaw S ∧ innerLaw S′) (rSplit S ∧ rSplit S′)

-- S(Γ): the meet over the marks of a₁ … aₙ. With no hom (n = 0) there
-- is no inner letter, and every setting gives the same free object.
meet : List SMark → Setting
meet []       = setting true true
meet (m ∷ ms) = laws m ∧S meet ms

------------------------------------------------------------------------
-- Booleans.

private
  ∧-in : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-in {true} _ q = q

------------------------------------------------------------------------
-- Marking every object with S recovers the file setting S.

data Every {A : Set} (P : A → Set) : List A → Set where
  []  : Every P []
  _∷_ : ∀ {x xs} → P x → Every P xs → Every P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

private
  ∧-idem : ∀ b → b ∧ b ≡ b
  ∧-idem true  = refl
  ∧-idem false = refl

  ∧-true : ∀ b → b ∧ true ≡ b
  ∧-true true  = refl
  ∧-true false = refl

∧S-top : ∀ S → S ∧S setting true true ≡ S
∧S-top (setting l r) = cong₂ setting (∧-true l) (∧-true r)

∧S-idem : ∀ S → S ∧S S ≡ S
∧S-idem (setting l r) = cong₂ setting (∧-idem l) (∧-idem r)

uniform-recovers : ∀ S m ms → laws m ≡ S → Every (λ m′ → laws m′ ≡ S) ms →
                   meet (m ∷ ms) ≡ S
uniform-recovers S m [] e [] = trans (∧S-top (laws m)) e
uniform-recovers S m (m′ ∷ ms) e (e′ ∷ es) =
  trans (cong (laws m ∧S_) (uniform-recovers S m′ ms e′ es))
        (trans (cong (_∧S S) e) (∧S-idem S))

-- The four old settings, each as a uniform marking of a two-object head.
old-vS   : meet (smark false false noM ∷ smark false false noM ∷ []) ≡ setting false false
old-vS   = refl
old-iccS : meet (smark true  false noM ∷ smark true  false noM ∷ []) ≡ setting true false
old-iccS = refl
old-rspS : meet (smark false true  noM ∷ smark false true  noM ∷ []) ≡ setting false true
old-rspS = refl
old-allS : meet (smark true  true  noM ∷ smark true  true  noM ∷ []) ≡ setting true true
old-allS = refl

------------------------------------------------------------------------
-- Every object of the head carries every law of S(Γ). This is the
-- step of the soundness argument: a model whose object γ(aᵢ) carries
-- the marks of aᵢ satisfies each law of S(Γ) in every hom landing in
-- γ(aᵢ), so its map out of F_V(Γ) factors through F_{V+S(Γ)}(Γ).

meet-lb : ∀ ms m → Any (λ m′ → m′ ≡ m) ms → meet ms ≤S laws m
meet-lb (m ∷ ms) .m (here refl) =
  (λ p → ∧-fst {innerLaw (laws m)} p) , (λ p → ∧-fst {rSplit (laws m)} p)
meet-lb (m′ ∷ ms) m (there a) with meet-lb ms m a
... | il , rr =
  (λ p → il (∧-snd {innerLaw (laws m′)} p)) ,
  (λ p → rr (∧-snd {rSplit (laws m′)} p))

------------------------------------------------------------------------
-- Stronger marks give a larger setting.

_≤M_ : SMark → SMark → Set
m ≤M m′ = laws m ≤S laws m′

data Pointwise {A : Set} (R : A → A → Set) : List A → List A → Set where
  []  : Pointwise R [] []
  _∷_ : ∀ {x y xs ys} → R x y → Pointwise R xs ys → Pointwise R (x ∷ xs) (y ∷ ys)

meet-mono : ∀ {ms ms′} → Pointwise _≤M_ ms ms′ → meet ms ≤S meet ms′
meet-mono [] = (λ p → p) , (λ p → p)
meet-mono {m ∷ ms} {m′ ∷ ms′} ((il , rr) ∷ ps) with meet-mono ps
... | il′ , rr′ =
  (λ p → ∧-in {innerLaw (laws m′)} (il (∧-fst {innerLaw (laws m)} p))
                                   (il′ (∧-snd {innerLaw (laws m)} p))) ,
  (λ p → ∧-in {rSplit (laws m′)} (rr (∧-fst {rSplit (laws m)} p))
                                 (rr′ (∧-snd {rSplit (laws m)} p)))

------------------------------------------------------------------------
-- The rule: the uniform marks rules of MarksRepaired, with the setting
-- computed from the head. `sm` lists a split mark for each component,
-- indexed like `cs`; the head's hm is read at the indices objs h, minus
-- a₀. Not mechanized: that `str` in `sm` agrees with `om` in `cs`
-- ((COH-ord) still reads `cs`), by convention of the encoding.

nthS : Nat → List SMark → SMark
nthS _       []       = smark false false noM
nthS zero    (m ∷ _)  = m
nthS (suc n) (_ ∷ ms) = nthS n ms

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

tailL : ∀ {A : Set} → List A → List A
tailL []       = []
tailL (_ ∷ xs) = xs

-- the marks of a₁ … aₙ
headMarks : Head → List SMark → List SMark
headMarks h sm = mapL (λ i → nthS i sm) (tailL (Head.objs h))

invM : List SMark → Head → List Comp → Bool
invM sm h cs = invU (meet (headMarks h sm)) h cs

-- Stronger marks at the head's objects give more judgments.
invM-mono : ∀ {sm sm′} h → Pointwise _≤M_ (headMarks h sm) (headMarks h sm′) → ∀ cs →
            T (invM sm h cs) → T (invM sm′ h cs)
invM-mono h le cs = setting-mono′ (meet-mono le) h cs

------------------------------------------------------------------------
-- Directed Eckmann–Hilton (spec §3.6 Example (a)) with split marks.
-- Components: X, C, a, b; C is component 1, the head's objects are
-- X (a₀) and C (a₁), and the elementary inner interchanger has left
-- input a (2) and right input b (3).

private
  ehHead : Head
  ehHead = head innerC [] [] false (just (2 , 3)) 1 (0 ∷ 1 ∷ [])

  unm inv : Comp
  unm = comp (ip false false false) noM
  inv = comp (ip true false false) noM

  csA csB : List Comp
  csA = unm ∷ unm ∷ inv ∷ unm ∷ []     -- a inv
  csB = unm ∷ unm ∷ unm ∷ inv ∷ []     -- b inv

  -- split marks on C only; X carries the opposite marks, which must
  -- not matter (a₀ is the target of no hom)
  onC : Bool → Bool → List SMark
  onC l r = smark (not l) (not r) noM ∷ smark l r noM ∷
            smark false false noM ∷ smark false false noM ∷ []

eh-none : invM (onC false false) ehHead csA ≡ false
eh-none = refl

eh-lsplit : invM (onC true false) ehHead csA ≡ true
eh-lsplit = refl

eh-rsplit : invM (onC false true) ehHead csB ≡ true
eh-rsplit = refl

-- R alone needs the right input b invertible; here only a is.
eh-rsplit-wrong-side : invM (onC false true) ehHead csA ≡ false
eh-rsplit-wrong-side = refl

-- lsplit alone needs a; here only b is.
eh-lsplit-wrong-side : invM (onC true false) ehHead csB ≡ false
eh-lsplit-wrong-side = refl

------------------------------------------------------------------------
-- Degree 4: both sides of a split law are pure inner, so a predicate
-- closed under the pure-inner constructors holds of both sides.

module Degree4 (G1 G2 G3 G4 : Set) where
  open SL.PartA G1 G2 G3 G4
  open import CaTTExp.Join.SepAlgebra using (module Theory)
  open Theory G1 G2 G3 G4

  record Closed (Tr : T4 → Set) : Set where
    field
      c-id  : ∀ F → Tr (id4 F)
      c-ι   : ∀ F G → Tr (ι F G)
      c-·   : ∀ {X Y} → Tr X → Tr Y → Tr (X · Y)
      c-ctx : ∀ p {X} q → Tr X → Tr (ctx p X q)
      c-wl4 : ∀ a {X} → Tr X → Tr (wl4 a X)
      c-wr4 : ∀ {X} a → Tr X → Tr (wr4 X a)
      c-w1L : ∀ f {X} → Tr X → Tr (w1L₄ f X)
      c-w1R : ∀ {X} f → Tr X → Tr (w1R₄ X f)

  inner-closed : ∀ {Tr} → Closed Tr → ∀ {X} → Inner4 X → Tr X
  inner-closed C (i-id F)      = Closed.c-id C F
  inner-closed C (i-ι F G)     = Closed.c-ι C F G
  inner-closed C (i-· x y)     = Closed.c-· C (inner-closed C x) (inner-closed C y)
  inner-closed C (i-ctx p q x) = Closed.c-ctx C p q (inner-closed C x)
  inner-closed C (i-wl4 a x)   = Closed.c-wl4 C a (inner-closed C x)
  inner-closed C (i-wr4 a x)   = Closed.c-wr4 C a (inner-closed C x)
  inner-closed C (i-w1L f x)   = Closed.c-w1L C f (inner-closed C x)
  inner-closed C (i-w1R f x)   = Closed.c-w1R C f (inner-closed C x)

  law-trivial : ∀ {Tr} → Closed Tr → ∀ {sw X Y} → Law sw X Y → Tr X × Tr Y
  law-trivial C l with law-inner l
  ... | x , y = inner-closed C x , inner-closed C y
