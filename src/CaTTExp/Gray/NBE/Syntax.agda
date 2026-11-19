------------------------------------------------------------------------
-- The N/β/η rewriting on 1-cells of the Gray-monoidal biclosed
-- 2-category 𝒢 (reading I), as an inductive one-step relation (D18).
--
-- Source: notes/conjectures/answered/gray-biclosed-coherence-2026-11-19.md,
-- Followup 2 §1.1–1.2.  An arrow word is a list of context-decorated
-- triples (L, q, R), with q a generator, an evaluation e_{a,Z} or a
-- curry κ_a(f) whose body f is again a word.  A tag a is a direction
-- d ∈ {L, R} and a formula A, with
--
--     T_{(L,A)}(X) = A ⊗ X,   T_{(R,A)}(X) = X ⊗ A.
--
-- The syntax is parametric in the type of formula factors and of
-- generator labels, so every result holds for every signature.  It
-- carries no source annotation on curries (the X of the checking
-- module), matching the system whose confluence is claimed; formulas
-- are lists, so tensor associativity is built in.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Syntax (Fac G : Set) where

open import CaTTExp.Gray.NBE.Base

Formula : Set
Formula = List Fac

data Dir : Set where
  Ld Rd : Dir

mutual
  data Prim : Set where
    gen : G → Prim
    ev  : Dir → Formula → Formula → Prim
    cur : Dir → Formula → Formula → List Triple → Prim

  data Triple : Set where
    tri : Formula → Prim → Formula → Triple

Word : Set
Word = List Triple

-- Whiskering a triple by a tensor context (P, S).
inCtx : Formula → Formula → Triple → Triple
inCtx P S (tri l q r) = tri (P ++ l) q (r ++ S)

-- The context of T_a: (A, ∅) for a left tag, (∅, A) for a right tag.
pre : Dir → Formula → Formula
pre Ld A = A
pre Rd A = []

post : Dir → Formula → Formula
post Ld A = []
post Rd A = A

wrap : Dir → Formula → Triple → Triple
wrap d A = inCtx (pre d A) (post d A)

evT : Dir → Formula → Formula → Triple
evT d A Z = tri [] (ev d A Z) []

------------------------------------------------------------------------
-- One-step reduction.  Matching side conditions are equations
-- hypotheses, so that the left-hand sides are constructor patterns.

infix 4 _⟶_
data _⟶_ : Word → Word → Set where
  -- (N)  D[g] ; C[κ_a(f)]  ⟶  C[κ_a(T_a[D₀[g]] ; f)],  D = C ∘ D₀
  N : ∀ {DL DR CL CR D0L D0R q d A Z b w}
    → DL ≡ CL ++ D0L → DR ≡ D0R ++ CR
    → tri DL q DR ∷ tri CL (cur d A Z b) CR ∷ w
      ⟶ tri CL (cur d A Z (wrap d A (tri D0L q D0R) ∷ b)) CR ∷ w
  -- (β)  C[T_a[κ_a(f)]] ; C[e_{a,Z}]  ⟶  C[f]
  β : ∀ {l r CL CR d A Z b w}
    → l ≡ CL ++ pre d A → r ≡ post d A ++ CR
    → tri l (cur d A Z b) r ∷ tri CL (ev d A Z) CR ∷ w
      ⟶ map (inCtx CL CR) b ++ w
  -- (η)  C[κ_a(T_a[g] ; e_{a,Z})]  ⟶  C[g]
  η : ∀ {CL CR d A Z b g w}
    → b ≡ map (wrap d A) g ++ (evT d A Z ∷ [])
    → tri CL (cur d A Z b) CR ∷ w ⟶ map (inCtx CL CR) g ++ w
  -- congruences: later in the word, and inside a curry body
  skip : ∀ {t w w'} → w ⟶ w' → t ∷ w ⟶ t ∷ w'
  body : ∀ {l r d A Z b b' w} → b ⟶ b'
    → tri l (cur d A Z b) r ∷ w ⟶ tri l (cur d A Z b') r ∷ w

infix  4 _⟶*_
infixr 5 _◅_
data _⟶*_ : Word → Word → Set where
  ε   : ∀ {w} → w ⟶* w
  _◅_ : ∀ {u v w} → u ⟶ v → v ⟶* w → u ⟶* w

_◅◅_ : ∀ {u v w} → u ⟶* v → v ⟶* w → u ⟶* w
ε        ◅◅ q = q
(s ◅ p)  ◅◅ q = s ◅ (p ◅◅ q)

-- Strong normalisation: no infinite reduction sequence from w.
SN : Word → Set
SN = Acc (λ v w → w ⟶ v)
