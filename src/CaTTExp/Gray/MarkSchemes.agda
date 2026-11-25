------------------------------------------------------------------------
-- Mark schemes: invertibility as one declared coinductive tower among
-- others (notes/mark-schemes.md, ledger S35).
--
-- A *scheme* is a finite marked context extension over a generic cell
-- t of a fixed dimension: clause cells c₁ … cₖ whose types are written
-- over the disk context Dⁿ ▸ t ▸ c₁ ▸ …, each clause optionally marked
-- with a scheme again. Read coinductively, marking a variable with a
-- scheme puts the whole infinite tower into the context. A scheme
-- presentation in the spec is dimension-generic (by suspension); here
-- each scheme is presented at dimensions 1 and 2, and the clause marks
-- that land in dimension 3 name a scheme with no encoded presentation
-- (`InvHi`, `RInvHi`), which only accepts the evidence forms that do not
-- need one.
--
-- Evidence that t carries scheme S:
--   hyp            t is a variable marked S in the context
--   old e          for the invertibility schemes only: the evidence layer
--                  of Gray.MarksSaturation (the `inv` judgment, inv-intro,
--                  can); this is where Inv's built-in closure rules enter
--   intro cs es    the clause cells cs, type-checked with the certified
--                  checker and matched against the instantiated clause
--                  types, with evidence es for the marked clauses
--
-- Results.
--  * `inv₁-instance`, `inv₂-instance`: for every marked context, term t,
--    candidate cells s, s′, l, r and S21 evidence eL, eR, the generic
--    intro of the Inv scheme, with the unit cells' evidence given as
--    `old eL`, `old eR`, decides exactly what ICaTT's inv-intro (`inv₁`,
--    `inv₂` of Gray.MarksSaturation) decides. So inv-intro is the
--    generic intro of one scheme. Scheme evidence of other forms on the
--    unit cells (`hyp`, nested `intro`) is not covered by the theorem;
--    it can accept more, because scheme hypotheses are hypotheses the
--    S21 layer does not see.
--  * The Inv scheme reaches itself one dimension up: Inv₁'s unit cells
--    are marked Inv₂ (example at the end, with hypotheses on l and r).
--  * (S-coh′) (notes/mark-schemes.md §9.1): evidence `cohS` for a
--    coherence-case coh, accepted when the scheme passes the check at the
--    generic identity (`genericOK`). Inv and RInv pass; P₁ (`Back₂`, the
--    counterexample to the earlier (S-coh) sketch) fails, and 1_f is
--    refused for it. That the generic check implies the rule for every
--    coherence-case coh is on paper (§9.1); the dimension-3 names reuse
--    the dimension-2 check by suspension invariance, assumed.
--  * RInv, "t has a right inverse whose counit has a right inverse, and
--    so on", evaluated on two contexts, including a two-level tower
--    closed by a hypothesis at dimension 3. That the `inv` marks cannot
--    express RInv is an informal remark (notes/mark-schemes.md §3), not
--    a formal result here: the non-derivability of `x inv` is checked
--    with no inv marks in the context.
--
-- Scope, stated honestly:
--  * Dimensions 1 and 2 only (no suspension), as in Gray.MarksSaturation.
--  * The scheme marks `sm` are assumed well-formed: `hyp` does not check
--    the dimension of the marked variable, and `old e` does not check
--    the dimension of t (the S21 layer's `inv` is one predicate across
--    dimensions, so `old` only says that t is invertible). Scheme marks
--    and the inv marks `ms` are separate lists; a scheme mark never
--    feeds the `inv` judgment. As in Gray.MarksSaturation, t itself is
--    assumed well-typed; the clause cells are type-checked (`wt`).
--  * Generic projections (destructors) are not term formers here, since
--    the core syntax has none (ledger E4).
--  * No ∀-clauses (ps, grpd_k): their entailments are the existing rules
--    of Gray.Marks, reached through `old`.
--  * Soundness of the generic rules is on paper (notes/mark-schemes.md
--    §3): a scheme-marked variable is the infinite unfolded context,
--    and intro supplies its first level plus evidence for the rest.
------------------------------------------------------------------------
module CaTTExp.Gray.MarkSchemes where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Marks ∅
open import CaTTExp.Gray.Examples using (comp; idc; vcomp)
open import CaTTExp.Gray.MarksSaturation
  using (Ev; jud; inv₁; inv₂; checkEv; wt; eqTy; id2)

private
  v : Nat → Tm
  v = var

------------------------------------------------------------------------
-- Scheme names and presentations.

data SName : Set where
  Inv₁ Inv₂ InvHi    : SName
  RInv₁ RInv₂ RInvHi : SName
  Back₂              : SName   -- P₁ of mark-schemes.md §8: an arrow
                               -- from the ultimate target of t to its
                               -- ultimate source (t a 2-cell)

_==S_ : SName → SName → Bool
Inv₁   ==S Inv₁   = true
Inv₂   ==S Inv₂   = true
InvHi  ==S InvHi  = true
RInv₁  ==S RInv₁  = true
RInv₂  ==S RInv₂  = true
RInvHi ==S RInvHi = true
Back₂  ==S Back₂  = true
_      ==S _      = false

isInvName : SName → Bool
isInvName Inv₁  = true
isInvName Inv₂  = true
isInvName InvHi = true
isInvName _     = false

data CMark : Set where
  none : CMark
  sch  : SName → CMark

record Scheme : Set where
  constructor scheme
  field
    dimS    : Nat                 -- dimension of the generic cell t
    clauses : List (Ty × CMark)   -- types over Dⁿ ▸ t ▸ c₁ ▸ …
open Scheme public

-- Disk contexts: D¹ = a0 b1 t2;  D² = X0 Y1 f2 g3 t4.
-- Inv(t : u → v) := s, s′ : v → u;  l : s;t → 1_v [Inv];  r : t;s′ → 1_u [Inv]
-- RInv(t : u → v) := s : v → u;  r : t;s → 1_u [RInv]
present : SName → Maybe Scheme
present Inv₁ = just (scheme 1
  ( (arr ⋆ (v 1) (v 0) , none)                                       -- s  3
  ∷ (arr ⋆ (v 1) (v 0) , none)                                       -- s′ 4
  ∷ (arr (arr ⋆ (v 1) (v 1)) (comp (v 1) (v 0) (v 3) (v 1) (v 2)) (idc (v 1))
      , sch Inv₂)                                                    -- l  5
  ∷ (arr (arr ⋆ (v 0) (v 0)) (comp (v 0) (v 1) (v 2) (v 0) (v 4)) (idc (v 0))
      , sch Inv₂)                                                    -- r  6
  ∷ []))
present Inv₂ = just (scheme 2
  ( (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 2) , none)                     -- s  5
  ∷ (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 2) , none)                     -- s′ 6
  ∷ (arr (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 3))
         (vcomp (v 0) (v 1) (v 3) (v 2) (v 5) (v 3) (v 4)) (id2 (v 0) (v 1) (v 3))
      , sch InvHi)                                                    -- l  7
  ∷ (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2))
         (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 2) (v 6)) (id2 (v 0) (v 1) (v 2))
      , sch InvHi)                                                    -- r  8
  ∷ []))
present RInv₁ = just (scheme 1
  ( (arr ⋆ (v 1) (v 0) , none)                                       -- s  3
  ∷ (arr (arr ⋆ (v 0) (v 0)) (comp (v 0) (v 1) (v 2) (v 0) (v 3)) (idc (v 0))
      , sch RInv₂)                                                    -- r  4
  ∷ []))
present RInv₂ = just (scheme 2
  ( (arr (arr ⋆ (v 0) (v 1)) (v 3) (v 2) , none)                     -- s  5
  ∷ (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2))
         (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 2) (v 5)) (id2 (v 0) (v 1) (v 2))
      , sch RInvHi)                                                   -- r  6
  ∷ []))
present Back₂ = just (scheme 2
  ( (arr ⋆ (v 1) (v 0) , none)                                       -- c  5
  ∷ []))
present InvHi  = nothing
present RInvHi = nothing

-- The boundary of a cell of the given dimension, in disk-context order.
bd : Nat → Maybe Ty → Maybe (List Tm)
bd 1 (just (arr ⋆ a b))           = just (a ∷ b ∷ [])
bd 2 (just (arr (arr ⋆ X Y) f g)) = just (X ∷ Y ∷ f ∷ g ∷ [])
bd _ _                            = nothing

------------------------------------------------------------------------
-- (S-coh′) at the generic identity (notes/mark-schemes.md §9.1).
-- For a scheme of dimension 2, take the generic identity t₀ = 1_f over
-- D¹ = (x0, y1, f2), and choose each clause cell as the coh over D¹ of
-- the instantiated clause type. The scheme passes when every such coh is
-- accepted by the certified checker and is in the coherence case.
-- Coherence-case cells of dimension 1 do not exist in two-tier L, so the
-- check is made at dimension 2. The dimension-3 names inherit the check
-- of their dimension-2 presentation: that is the suspension-invariance
-- assumption of §9.1, stated there and not encoded.

D¹ : Ctx
D¹ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1)

t₀ : Tm
t₀ = id2 (v 0) (v 1) (v 2)

isCohCase : Tm → Bool
isCohCase (coh Θ (arr A p q) γ) = cohCase Θ A p q
isCohCase _                     = false

genCells : List (Ty × CMark) → List Tm → List Tm
genCells []             acc = acc
genCells ((A , _) ∷ cl) acc =
  genCells cl (acc ++ (coh D¹ (A [ ⟪ v 0 ∷ v 1 ∷ v 2 ∷ v 2 ∷ t₀ ∷ acc ⟫ ]ty) (idₛ D¹) ∷ []))

genOK : Maybe Scheme → Bool
genOK (just (scheme 2 cl)) = all (λ c → wt D¹ c ∧ isCohCase c) (genCells cl [])
genOK _                    = false

genericOK : SName → Bool
genericOK Inv₂   = genOK (present Inv₂)
genericOK InvHi  = genOK (present Inv₂)     -- suspension (assumed)
genericOK RInv₂  = genOK (present RInv₂)
genericOK RInvHi = genOK (present RInv₂)    -- suspension (assumed)
genericOK Back₂  = genOK (present Back₂)
genericOK _      = false                    -- dimension 1: never needed

schemeDim : SName → Nat
schemeDim Inv₁  = 1
schemeDim RInv₁ = 1
schemeDim InvHi  = 3
schemeDim RInvHi = 3
schemeDim _     = 2

dimIs : Nat → Maybe Ty → Bool
dimIs n (just A) = dim A ==ℕ n
dimIs n nothing  = false

------------------------------------------------------------------------
-- Evidence and the generic checker.

data SEv : Set where
  hyp   : SEv
  old   : Ev → SEv
  intro : List Tm → List SEv → SEv
  cohS  : SEv          -- (S-coh′): t is a coherence-case coh

SMarks : Set
SMarks = List (Nat × SName)

andL : List Bool → Bool
andL []       = true
andL (b ∷ bs) = b ∧ andL bs

markedVar : SMarks → SName → Tm → Bool
markedVar sm n (var i) = any (λ m → (fst m ==ℕ i) ∧ (snd m ==S n)) sm
markedVar sm n _       = false

-- the clause types match the cells, under σ = boundary, t, cells
tysOK : Ctx → Sub → List (Ty × CMark) → List Tm → List Bool
tysOK Γ σ []             []       = []
tysOK Γ σ ((A , _) ∷ cl) (c ∷ cs) = eqTy (typeOf Γ c) (A [ σ ]ty) ∷ tysOK Γ σ cl cs
tysOK Γ σ _              _        = false ∷ []

mutual
  checkS : SMarks → Marks → Ctx → SName → SEv → Tm → Bool
  checkS sm ms Γ n hyp           t = markedVar sm n t
  checkS sm ms Γ n (old e)       t = isInvName n ∧ checkEv ms Γ t e
  checkS sm ms Γ n (intro cs es) t = introS sm ms Γ (present n) t (typeOf Γ t) cs es
  checkS sm ms Γ n cohS          t =
    genericOK n ∧ wt Γ t ∧ isCohCase t ∧ dimIs (schemeDim n) (typeOf Γ t)

  introS : SMarks → Marks → Ctx → Maybe Scheme → Tm → Maybe Ty
         → List Tm → List SEv → Bool
  introS sm ms Γ nothing  t A cs es = false
  introS sm ms Γ (just S) t A cs es = introB sm ms Γ S t (bd (dimS S) A) cs es

  introB : SMarks → Marks → Ctx → Scheme → Tm → Maybe (List Tm)
         → List Tm → List SEv → Bool
  introB sm ms Γ S t nothing   cs es = false
  introB sm ms Γ S t (just bs) cs es =
    andL (map (wt Γ) cs
          ++ tysOK Γ ⟪ bs ++ (t ∷ cs) ⟫ (clauses S) cs
          ++ mksOK sm ms Γ (clauses S) cs es)

  -- evidence for the marked clauses, in order
  mksOK : SMarks → Marks → Ctx → List (Ty × CMark) → List Tm → List SEv → List Bool
  mksOK sm ms Γ []                  []       []       = []
  mksOK sm ms Γ ((_ , none)  ∷ cl)  (c ∷ cs) es       = mksOK sm ms Γ cl cs es
  mksOK sm ms Γ ((_ , sch n) ∷ cl)  (c ∷ cs) (e ∷ es) = checkS sm ms Γ n e c ∷ mksOK sm ms Γ cl cs es
  mksOK sm ms Γ _                   _        _        = false ∷ []

------------------------------------------------------------------------
-- Inv is an instance: its generic intro is ICaTT's inv-intro.

private
  ∧-true : ∀ b → b ∧ true ≡ b
  ∧-true true  = refl
  ∧-true false = refl

inv₁-instance : ∀ sm ms Γ t s s′ l r eL eR →
  checkS sm ms Γ Inv₁ (intro (s ∷ s′ ∷ l ∷ r ∷ []) (old eL ∷ old eR ∷ [])) t
  ≡ checkEv ms Γ t (inv₁ s s′ l r eL eR)
inv₁-instance sm ms Γ t s s′ l r eL eR with typeOf Γ t
... | nothing                 = refl
... | just ⋆                  = refl
... | just (arr ⋆ a b)        =
  cong (λ z → wt Γ s ∧ wt Γ s′ ∧ wt Γ l ∧ wt Γ r
            ∧ eqTy (typeOf Γ s)  (arr ⋆ b a)
            ∧ eqTy (typeOf Γ s′) (arr ⋆ b a)
            ∧ eqTy (typeOf Γ l)  (arr (arr ⋆ b b) (comp b a s b t) (idc b))
            ∧ eqTy (typeOf Γ r)  (arr (arr ⋆ a a) (comp a b t a s′) (idc a))
            ∧ checkEv ms Γ l eL ∧ z)
       (∧-true (checkEv ms Γ r eR))
... | just (arr (arr A c d) f g) = refl

inv₂-instance : ∀ sm ms Γ t s s′ l r eL eR →
  checkS sm ms Γ Inv₂ (intro (s ∷ s′ ∷ l ∷ r ∷ []) (old eL ∷ old eR ∷ [])) t
  ≡ checkEv ms Γ t (inv₂ s s′ l r eL eR)
inv₂-instance sm ms Γ t s s′ l r eL eR with typeOf Γ t
... | nothing                     = refl
... | just ⋆                      = refl
... | just (arr ⋆ a b)            = refl
... | just (arr (arr ⋆ X Y) f g)  =
  cong (λ z → wt Γ s ∧ wt Γ s′ ∧ wt Γ l ∧ wt Γ r
            ∧ eqTy (typeOf Γ s)  (arr (arr ⋆ X Y) g f)
            ∧ eqTy (typeOf Γ s′) (arr (arr ⋆ X Y) g f)
            ∧ eqTy (typeOf Γ l)  (arr (arr (arr ⋆ X Y) g g) (vcomp X Y g f s g t) (id2 X Y g))
            ∧ eqTy (typeOf Γ r)  (arr (arr (arr ⋆ X Y) f f) (vcomp X Y f g t f s′) (id2 X Y f))
            ∧ checkEv ms Γ l eL ∧ z)
       (∧-true (checkEv ms Γ r eR))
... | just (arr (arr (arr A c d) h k) f g) = refl

------------------------------------------------------------------------
-- RInv: right inverses all the way up (that inv marks cannot express it
-- is informal, see the header).
-- Γ₃: a0 b1 x2 : a → b, s3 : b → a, r4 : x;s ⇒ 1_a, r marked RInv₂.

private
  a b x s r s₂ ρ₂ : Tm
  a = v 0 ; b = v 1 ; x = v 2 ; s = v 3 ; r = v 4 ; s₂ = v 5 ; ρ₂ = v 6

  xs : Tm
  xs = comp a b x a s

Γ₃ : Ctx
Γ₃ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ a b ▸ arr ⋆ b a ▸ arr (arr ⋆ a a) xs (idc a)

_ : is-just (checkCtx Γ₃) ≡ true
_ = refl

sm₃ : SMarks
sm₃ = (4 , RInv₂) ∷ []

-- x carries RInv, from the clause cells s, r and the hypothesis on r.
_ : checkS sm₃ [] Γ₃ RInv₁ (intro (s ∷ r ∷ []) (hyp ∷ [])) x ≡ true
_ = refl

-- x is not derivably inv (checked with no inv marks in the context).
_ : ([] , Γ₃) ⊢ x inv ≡ false
_ = refl
-- The same cells do not make an Inv intro: there is no left unit
-- s;x ⇒ 1_b, and r (a right unit x;s ⇒ 1_a) does not fit that clause.
_ : checkS ((4 , Inv₂) ∷ []) [] Γ₃ Inv₁
      (intro (s ∷ s ∷ r ∷ r ∷ []) (hyp ∷ hyp ∷ [])) x ≡ false
_ = refl

-- Wrong data is rejected: no mark on r; the wrong cell in place of s.
_ : checkS [] [] Γ₃ RInv₁ (intro (s ∷ r ∷ []) (hyp ∷ [])) x ≡ false
_ = refl
_ : checkS sm₃ [] Γ₃ RInv₁ (intro (x ∷ r ∷ []) (hyp ∷ [])) x ≡ false
_ = refl
-- A scheme with no presentation cannot be introduced.
_ : checkS sm₃ [] Γ₃ RInvHi (intro [] []) x ≡ false
_ = refl

-- Two levels: r is itself RInv by data, s₂ : 1_a ⇒ x;s and
-- ρ₂ : r;s₂ ⇛ 1_{x;s}, with the hypothesis only at dimension 3.
Γ₄ : Ctx
Γ₄ = Γ₃ ▸ arr (arr ⋆ a a) (idc a) xs
        ▸ arr (arr (arr ⋆ a a) xs xs) (vcomp a a xs (idc a) r xs s₂) (id2 a a xs)

_ : is-just (checkCtx Γ₄) ≡ true
_ = refl

sm₄ : SMarks
sm₄ = (6 , RInvHi) ∷ []

_ : checkS sm₄ [] Γ₄ RInv₁ (intro (s ∷ r ∷ []) (intro (s₂ ∷ ρ₂ ∷ []) (hyp ∷ []) ∷ [])) x ≡ true
_ = refl
-- the inner level is checked: with the hypothesis on the wrong cell it fails
_ : checkS ((5 , RInvHi) ∷ []) [] Γ₄ RInv₁ (intro (s ∷ r ∷ []) (intro (s₂ ∷ ρ₂ ∷ []) (hyp ∷ []) ∷ [])) x ≡ false
_ = refl

------------------------------------------------------------------------
-- The Inv scheme reproduces the Γ₁ example of Gray.MarksSaturation
-- (an equivalence given by data) through the generic intro.

private
  Γ₁ : Ctx
  Γ₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ a b ▸ arr ⋆ b a
         ▸ arr (arr ⋆ b b) (comp b a s b x) (idc b)
         ▸ arr (arr ⋆ a a) (comp a b x a s) (idc a)
  y l₁ r₁ : Tm
  y = v 3 ; l₁ = v 4 ; r₁ = v 5

_ : checkS [] ((4 , minv) ∷ (5 , minv) ∷ []) Γ₁ Inv₁
      (intro (y ∷ y ∷ l₁ ∷ r₁ ∷ []) (old jud ∷ old jud ∷ [])) x ≡ true
_ = refl

-- Inside the scheme language: with l and r marked Inv₂ as scheme
-- hypotheses (and no inv marks), x carries Inv₁.
_ : checkS ((4 , Inv₂) ∷ (5 , Inv₂) ∷ []) [] Γ₁ Inv₁
      (intro (y ∷ y ∷ l₁ ∷ r₁ ∷ []) (hyp ∷ hyp ∷ [])) x ≡ true
_ = refl
-- Control: marked with the wrong scheme, it fails.
_ : checkS ((4 , RInv₂) ∷ (5 , RInv₂) ∷ []) [] Γ₁ Inv₁
      (intro (y ∷ y ∷ l₁ ∷ r₁ ∷ []) (hyp ∷ hyp ∷ [])) x ≡ false
_ = refl

------------------------------------------------------------------------
-- (S-coh′) examples (notes/mark-schemes.md §9.1).

-- The generic check: Inv and RInv pass, P₁ (Back₂) fails. Its clause
-- cell would be a coh over D¹ of type y → x, which the checker rejects:
-- this is the counterexample to the old (S-coh) sketch, whose premise
-- (a clause type built from the boundary of t) P₁ satisfies.
_ : genericOK Inv₂ ≡ true
_ = refl
_ : genericOK RInv₂ ≡ true
_ = refl
_ : genericOK Back₂ ≡ false
_ = refl
_ : wt D¹ (coh D¹ (arr ⋆ (v 1) (v 0)) (idₛ D¹)) ≡ false
_ = refl

-- Coherence-case cells carry Inv and RInv by cohS: the identity 1_f and
-- the left unitor 1_x;f ⇒ f over D¹.
unitor : Tm
unitor = coh D¹ (arr (arr ⋆ (v 0) (v 1)) (comp (v 0) (v 0) (idc (v 0)) (v 1) (v 2)) (v 2)) (idₛ D¹)

_ : checkS [] [] D¹ Inv₂ cohS t₀ ≡ true
_ = refl
_ : checkS [] [] D¹ RInv₂ cohS t₀ ≡ true
_ = refl
_ : checkS [] [] D¹ Inv₂ cohS unitor ≡ true
_ = refl
-- … but 1_f does not carry P₁, and cohS refuses it.
_ : checkS [] [] D¹ Back₂ cohS t₀ ≡ false
_ = refl
-- cohS needs a coherence-case cell: a 2-cell variable is refused.
_ : checkS [] [] Γ₃ RInv₂ cohS r ≡ false
_ = refl
-- cohS closes a tower one level down: 1_f carries RInv₂ by intro, with
-- right inverse 1_f and counit the coherence 1_f;1_f ⇛ 1_f, whose
-- dimension-3 tower is given by cohS. No hypothesis is used.
ρ₀ : Tm
ρ₀ = coh D¹ (arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2))
                 (vcomp (v 0) (v 1) (v 2) (v 2) t₀ (v 2) t₀) t₀) (idₛ D¹)

_ : checkS [] [] D¹ RInv₂ (intro (t₀ ∷ ρ₀ ∷ []) (cohS ∷ [])) t₀ ≡ true
_ = refl
