module CaTTExp.Surface.SplitCoverReturn where

open import CaTTExp.Prelude

-- Equality in a set quotient presented by generating pairs.
module Closure {A : Set} (Step : A → A → Set) where
  data Path : A → A → Set where
    stop : ∀ {x} → Path x x
    along : ∀ {x y z} → Step x y → Path y z → Path x z
    against : ∀ {x y z} → Step y x → Path y z → Path x z

  transport : (D : A → Set) →
              (∀ {x y} → Step x y → D x → D y) →
              (∀ {x y} → Step x y → D y → D x) →
              ∀ {x y} → Path x y → D x → D y
  transport D f g stop d = d
  transport D f g (along s p) d = transport D f g p (f s d)
  transport D f g (against s p) d = transport D f g p (g s d)

module Attachment
  (Obj : Set) (_⇒_ : Obj → Obj → Set)
  (unit : ∀ {A} → A ⇒ A) (_∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C)
  (assoc : ∀ {A B C D} (h : C ⇒ D) (g : B ⇒ C) (f : A ⇒ B) →
           (h ∘ g) ∘ f ≡ h ∘ (g ∘ f))
  (left-unit : ∀ {A B} (f : A ⇒ B) → unit ∘ f ≡ f)
  (X : Obj → Set) (res : ∀ {A B} → A ⇒ B → X B → X A)
  (res-comp : ∀ {A B C} (u : A ⇒ B) (v : B ⇒ C) (x : X C) →
              res u (res v x) ≡ res (v ∘ u) x)
  (P : Obj) (Side : Set) (Q : Side → Obj)
  (inc : (s : Side) → Q s ⇒ P) (ret : (s : Side) → P ⇒ Q s)
  (split : (s : Side) → ret s ∘ inc s ≡ unit)
  (inputs : (s : Side) → X (Q s))
  (agree : ∀ {A} (s t : Side) (k : A ⇒ Q s) (l : A ⇒ Q t) →
           inc s ∘ k ≡ inc t ∘ l → res k (inputs s) ≡ res l (inputs t))
  where

  data Label (A : Obj) : Set where
    old : X A → Label A
    new : A ⇒ P → Label A

  data Glue {A : Obj} : Label A → Label A → Set where
    glue : (s : Side) (k : A ⇒ Q s) →
           Glue (old (res k (inputs s))) (new (inc s ∘ k))

  restrict : ∀ {A B} → A ⇒ B → Label B → Label A
  restrict u (old x) = old (res u x)
  restrict u (new f) = new (f ∘ u)

  Origin : ∀ {A} → X A → Label A → Set
  Origin a (old x) = x ≡ a
  Origin {A} a (new f) = Σ Side λ s → Σ (A ⇒ Q s) λ k →
                          (inc s ∘ k ≡ f) × (res k (inputs s) ≡ a)

  enter : ∀ {A} {a : X A} {x y} → Glue x y → Origin a x → Origin a y
  enter (glue s k) same = s , k , refl , same

  leave : ∀ {A} {a : X A} {x y} → Glue x y → Origin a y → Origin a x
  leave (glue s k) (t , l , same , value) =
    trans (agree s t k l (sym same)) value

  return-extension : ∀ {A B} (u : A ⇒ B) (a : X A) (b : Label B) →
                     Closure.Path Glue (old a) (restrict u b) →
                     Σ (X B) λ y → res u y ≡ a
  return-extension u a (old x) p =
    x , Closure.transport Glue (Origin a) enter leave p refl
  return-extension u a (new f) p
    with Closure.transport Glue (Origin a) enter leave p refl
  ... | s , k , same , value =
    res (ret s ∘ f) (inputs s) , trans (res-comp u (ret s ∘ f) (inputs s))
      (trans (cong (λ m → res m (inputs s)) (fits s k same)) value)
    where
    fits : ∀ s k → inc s ∘ k ≡ f ∘ u → (ret s ∘ f) ∘ u ≡ k
    fits s k same = trans (assoc (ret s) f u)
                    (trans (cong (ret s ∘_) (sym same))
                    (trans (sym (assoc (ret s) (inc s) k))
                    (trans (cong (_∘ k) (split s)) (left-unit k))))

-- Reachability in a graph pushout. A path may change summands whenever
-- a vertex of the common graph is glued to its image in the old graph.
module Reachability where
  data Walk {V : Set} (E : V → V → Set) : V → V → Set where
    stay : ∀ {a} → Walk E a a
    step : ∀ {a b c} → E a b → Walk E b c → Walk E a c

  append : ∀ {V} {E : V → V → Set} {a b c} →
           Walk E a b → Walk E b c → Walk E a c
  append stay q = q
  append (step e p) q = step e (append p q)

  module Pushout
    {X P K : Set} (old-edge : X → X → Set) (chart-edge : P → P → Set)
    (attach : K → X) (inc : K → P)
    (return-cut : ∀ a b → Walk chart-edge (inc a) (inc b) →
                          Walk old-edge (attach a) (attach b))
    where
    data Vertex : Set where
      prior : X → Vertex
      chart : P → Vertex

    data Move : Vertex → Vertex → Set where
      prior-step : ∀ {x y} → old-edge x y → Move (prior x) (prior y)
      chart-step : ∀ {x y} → chart-edge x y → Move (chart x) (chart y)
      enter : ∀ k → Move (prior (attach k)) (chart (inc k))
      leave : ∀ k → Move (chart (inc k)) (prior (attach k))

    Carry : X → Vertex → Set
    Carry x (prior y) = Walk old-edge x y
    Carry x (chart p) = Σ _ λ k → Walk old-edge x (attach k) × Walk chart-edge (inc k) p

    advance : ∀ {x u v} → Move u v → Carry x u → Carry x v
    advance (prior-step e) p = append p (step e stay)
    advance (chart-step e) (k , p , q) = k , p , append q (step e stay)
    advance (enter k) p = k , p , stay
    advance (leave l) (k , p , q) = append p (return-cut k l q)

    follow : ∀ {x u v} → Walk Move u v → Carry x u → Carry x v
    follow stay p = p
    follow (step e q) p = follow q (advance e p)

    return-walk : ∀ {x y} → Walk Move (prior x) (prior y) → Walk old-edge x y
    return-walk {x} p = follow {x = x} p stay
