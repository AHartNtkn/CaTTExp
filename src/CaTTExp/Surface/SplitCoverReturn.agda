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
