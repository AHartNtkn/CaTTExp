-- Exact-boundary return along a finite chain of spans. A fibre represents
-- a written type evaluated at the entire assignment to its earlier context.
module CaTTExp.Surface.SpanReturn where

open import CaTTExp.Prelude

record Span : Set₁ where
  field
    Left Middle Right : Set
    left  : Middle → Left
    right : Middle → Right

open Span

record TypeOver (s : Span) : Set₁ where
  field
    L : Left s → Set
    M : Middle s → Set
    R : Right s → Set
    toL : ∀ {m} → M m → L (left s m)
    toR : ∀ {m} → M m → R (right s m)
    liftL : ∀ m (x : L (left s m)) → ∃ λ y → toL {m} y ≡ x
    liftR : ∀ m (x : R (right s m)) → ∃ λ y → toR {m} y ≡ x

open TypeOver

empty : Span
empty = record { Left = ⊤ ; Middle = ⊤ ; Right = ⊤
               ; left = λ _ → tt ; right = λ _ → tt }

extend : (s : Span) → TypeOver s → Span
extend s a = record
  { Left = Σ (Left s) (L a)
  ; Middle = Σ (Middle s) (M a)
  ; Right = Σ (Right s) (R a)
  ; left = λ { (m , t) → left s m , toL a t }
  ; right = λ { (m , t) → right s m , toR a t } }

data Telescope : Span → Set₁ where
  start : Telescope empty
  add : ∀ {s} → Telescope s → (a : TypeOver s) → Telescope (extend s a)

assignment : ∀ {s} → Telescope s → (x : Left s) → ∃ λ m → left s m ≡ x
assignment start tt = tt , refl
assignment (add tel a) (x , t) with assignment tel x
... | m , refl with liftL a m t
...   | y , refl = (m , y) , refl

record Query : Set₁ where
  constructor query
  field
    Env : Set
    Cell : Env → Set

open Query

-- An assignment can move forward while a cell at its written boundary
-- can subsequently move back. The selected forward assignment is shared
-- with the backward map, including when the queried fibre is empty.
Return : Query → Query → Set
Return a b = (x : Env a) → ∃ λ y → Cell b y → Cell a x

span-return : ∀ {s} → Telescope s → (a : TypeOver s) →
              Return (query (Left s) (L a)) (query (Right s) (R a))
span-return {s} tel a x with assignment tel x
... | m , refl = right s m , λ t → toL a (fst (liftR a m t))

data Chain : Query → Query → Set₁ where
  done : ∀ {a} → Chain a a
  step : ∀ {a b c} → Return a b → Chain b c → Chain a c

chain-return : ∀ {a b} → Chain a b → Return a b
chain-return done x = x , λ t → t
chain-return (step f rest) x with f x
... | y , back with chain-return rest y
...   | z , earlier = z , λ t → back (earlier t)
