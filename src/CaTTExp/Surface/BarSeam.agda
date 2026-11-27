-- Return a diagram matched by paths at a fixed raw globular boundary.
module CaTTExp.Surface.BarSeam where

open import CaTTExp.Prelude

module Return
  (Vertex : Set) (Edge : Vertex → Vertex → Set)
  (Cell : Set) (Arrow : Cell → Cell → Set)
  (paste : ∀ {a b c} → Arrow a b → Arrow b c → Arrow a c)
  (Reading : Vertex → Set) (evaluate : ∀ {v} → Reading v → Cell)
  (compare : ∀ {v} (p q : Reading v) → Arrow (evaluate p) (evaluate q))
  (lift-edge : ∀ {u v} → Edge u v →
     Σ (Reading u) λ p → Σ (Reading v) λ q → evaluate p ≡ evaluate q)
  where

  data Zigzag : Vertex → Vertex → Set where
    stop : ∀ {u} → Zigzag u u
    along : ∀ {u v w} → Edge u v → Zigzag v w → Zigzag u w
    against : ∀ {u v w} → Edge v u → Zigzag v w → Zigzag u w

  transport : ∀ {u v} → Zigzag u v → (p : Reading u) (q : Reading v) →
              Arrow (evaluate p) (evaluate q)
  transport stop p q = compare p q
  transport (along e path) p q with lift-edge e
  ... | left , right , same =
    paste (compare p left)
          (subst (λ x → Arrow x (evaluate q)) (sym same) (transport path right q))
  transport (against e path) p q with lift-edge e
  ... | left , right , same =
    paste (compare p right)
          (subst (λ x → Arrow x (evaluate q)) same (transport path left q))

  matching : ∀ {u v a b} (p : Reading u) (q : Reading v)
             (left : Reading a) (right : Reading b) →
             Zigzag u a → Arrow (evaluate left) (evaluate right) → Zigzag b v →
             Arrow (evaluate p) (evaluate q)
  matching p q left right enter cell leave =
    paste (transport enter p left) (paste cell (transport leave right q))
