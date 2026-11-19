------------------------------------------------------------------------
-- The cut-inversion invariant: no reverse of an inner interchanger
-- (notes/conjectures/answered/lax-interchange-construction-or-
--  impossibility-2026-11-19.md, §6.3, (47)–(50)).
--
-- A 3-path that respects a positional cut h is a word of atomic steps,
-- each acting wholly before (L) or wholly after (R) the cut.
--
--   inv h = #{ i < j : step i is R, step j is L }               (47)
--
-- An inner move ι(U, V) replaces the block V ; U by U ; V, where the
-- positional interval of U precedes that of V. That forbids "V has an
-- L step and U has an R step" (precedes→ok), and then
--
--   inv before = inv after + D V U,                        (48), (49)
--
-- where D V U counts the pairs (v ∈ V on the R side, u ∈ U on the L
-- side) (inv-move). So inv never increases along inner moves
-- (inv-moves). At the cut of a proper elementary interchanger, U is
-- on the L side and V on the R side, so D V U ≥ 1 (proper), and no
-- sequence of inner moves can undo it (no-reverse). That is (50).
--
-- Not formalised here: that inv is invariant under the 3-equations
-- (the response argues it from "ba and ab share no interior state"),
-- and that a reverse cell consists of inner moves only (from positive
-- Gray images of r, t and input generators).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there; _≤_; z≤n; s≤s)

module CaTTExp.Join.CutInvariant where

data Side : Set where
  L R : Side

------------------------------------------------------------------------
-- Arithmetic and lists.

private
  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc zero    b c = refl
  +-assoc (suc a) b c = cong suc (+-assoc a b c)

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm zero    b = sym (+-zero b)
  +-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+-suc b a))

  ++-assoc : ∀ {A : Set} (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
  ++-assoc []       y z = refl
  ++-assoc (a ∷ x) y z = cong (a ∷_) (++-assoc x y z)

  ≤-refl : ∀ {n} → n ≤ n
  ≤-refl {zero}  = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans z≤n     _       = z≤n
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

  ≤-+ : ∀ a n → a ≤ a + n
  ≤-+ zero    n = z≤n
  ≤-+ (suc a) n = s≤s (≤-+ a n)

  ≤-step : ∀ {a b} → a ≤ b → a ≤ suc b
  ≤-step z≤n     = z≤n
  ≤-step (s≤s p) = s≤s (≤-step p)

  suc≰ : ∀ {n} → ¬ (suc n ≤ n)
  suc≰ {suc n} (s≤s p) = suc≰ p

------------------------------------------------------------------------
-- The invariant for one cut.

module Cut {Step : Set} (side : Step → Side) where

  lc : Side → Nat
  lc L = 1
  lc R = 0

  rc : Side → Nat → Nat
  rc L n = 0
  rc R n = n

  nL : List Step → Nat
  nL []      = 0
  nL (s ∷ w) = lc (side s) + nL w

  -- (47): pairs (R step, later L step).
  inv : List Step → Nat
  inv []      = 0
  inv (s ∷ w) = rc (side s) (nL w) + inv w

  -- One crossed pair.
  d : Step → Step → Nat
  d v u with side v | side u
  ... | R | L = 1
  ... | _ | _ = 0

  Ok : Step → Step → Set          -- "not (v on L and u on R)"
  Ok v u = ¬ ((side v ≡ L) × (side u ≡ R))

  private
    nL-swap : ∀ (x : List Step) v u y →
              nL (x ++ (v ∷ u ∷ y)) ≡ nL (x ++ (u ∷ v ∷ y))
    nL-swap []      v u y =
      trans (sym (+-assoc (lc (side v)) (lc (side u)) (nL y)))
      (trans (cong (_+ nL y) (+-comm (lc (side v)) (lc (side u))))
             (+-assoc (lc (side u)) (lc (side v)) (nL y)))
    nL-swap (s ∷ x) v u y = cong (lc (side s) +_) (nL-swap x v u y)

    swap₀ : ∀ v u y → Ok v u → inv (v ∷ u ∷ y) ≡ inv (u ∷ v ∷ y) + d v u
    swap₀ v u y ok with side v | side u
    ... | L | L = sym (+-zero _)
    ... | R | R = sym (+-zero _)
    ... | R | L = sym (+-suc (nL y + inv y) 0 ∙ cong suc (+-zero _))
      where
      _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      _∙_ = trans
    ... | L | R = ⊥-elim (ok (refl , refl))

  -- One adjacent transposition.
  transpose : ∀ (x : List Step) v u y → Ok v u →
              inv (x ++ (v ∷ u ∷ y)) ≡ inv (x ++ (u ∷ v ∷ y)) + d v u
  transpose []      v u y ok = swap₀ v u y ok
  transpose (s ∷ x) v u y ok =
    trans (cong₂ _+_ (cong (rc (side s)) (nL-swap x v u y)) (transpose x v u y ok))
          (sym (+-assoc (rc (side s) (nL (x ++ (u ∷ v ∷ y)))) _ (d v u)))

  Dv : List Step → Step → Nat
  Dv []      u = 0
  Dv (v ∷ V) u = d v u + Dv V u

  -- The pairs crossed by moving U before V.
  D : List Step → List Step → Nat
  D V []      = 0
  D V (u ∷ U) = Dv V u + D V U

  private
    past : ∀ (x V : List Step) u y → (∀ {v} → v ∈L V → Ok v u) →
           inv (x ++ (V ++ (u ∷ y))) ≡ inv (x ++ (u ∷ (V ++ y))) + Dv V u
    past x []      u y ok = sym (+-zero _)
    past x (v ∷ V) u y ok =
      trans (cong inv (sym (++-assoc x (v ∷ []) (V ++ (u ∷ y)))))
      (trans (past (x ++ (v ∷ [])) V u y (λ m → ok (there m)))
      (trans (cong (λ z → inv z + Dv V u) (++-assoc x (v ∷ []) (u ∷ (V ++ y))))
      (trans (cong (_+ Dv V u) (transpose x v u (V ++ y) (ok here)))
             (+-assoc (inv (x ++ (u ∷ v ∷ (V ++ y)))) (d v u) (Dv V u)))))

    swap4 : ∀ a b c → (a + b) + c ≡ a + (c + b)
    swap4 a b c = trans (+-assoc a b c) (cong (a +_) (+-comm b c))

  -- (48)/(49): an inner move lowers inv by exactly D V U.
  block : ∀ (x V U y : List Step) → (∀ {v u} → v ∈L V → u ∈L U → Ok v u) →
          inv (x ++ (V ++ (U ++ y))) ≡ inv (x ++ (U ++ (V ++ y))) + D V U
  block x V []      y ok = sym (+-zero _)
  block x V (u ∷ U) y ok =
    trans (past x V u (U ++ y) (λ m → ok m here))
    (trans (cong (λ z → inv z + Dv V u) (sym (++-assoc x (u ∷ []) (V ++ (U ++ y)))))
    (trans (cong (_+ Dv V u) (block (x ++ (u ∷ [])) V U y (λ mv mu → ok mv (there mu))))
    (trans (cong (λ z → (inv z + D V U) + Dv V u) (++-assoc x (u ∷ []) (U ++ (V ++ y))))
           (swap4 (inv (x ++ (u ∷ (U ++ (V ++ y))))) (D V U) (Dv V u)))))

  -- Inner moves at this cut.
  data Move : List Step → List Step → Set where
    move : ∀ x V U y → (∀ {v u} → v ∈L V → u ∈L U → Ok v u) →
           Move (x ++ (V ++ (U ++ y))) (x ++ (U ++ (V ++ y)))

  drop : ∀ {w w′} → Move w w′ → Nat
  drop (move x V U y _) = D V U

  inv-move : ∀ {w w′} (m : Move w w′) → inv w ≡ inv w′ + drop m
  inv-move (move x V U y ok) = block x V U y ok

  data Moves : List Step → List Step → Set where
    ε   : ∀ {w} → Moves w w
    _◅_ : ∀ {w w₁ w₂} → Move w w₁ → Moves w₁ w₂ → Moves w w₂

  -- inv never increases along inner moves.
  inv-moves : ∀ {w w′} → Moves w w′ → inv w′ ≤ inv w
  inv-moves ε = ≤-refl
  inv-moves (_◅_ {w} {w₁} m ms) =
    ≤-trans (inv-moves ms) (subst (inv w₁ ≤_) (sym (inv-move m)) (≤-+ (inv w₁) (drop m)))

  -- (50): a proper elementary instance strictly lowers inv ...
  proper : ∀ v V u U → side v ≡ R → side u ≡ L → 1 ≤ D (v ∷ V) (u ∷ U)
  proper v V u U sv su with side v | side u
  proper v V u U refl refl | R | L = s≤s z≤n

  -- ... so no sequence of inner moves reverses it.
  no-reverse : ∀ {w w′} (m : Move w w′) → 1 ≤ drop m → ¬ Moves w′ w
  no-reverse {w} {w′} m p back =
    suc≰ (≤-trans (subst (λ z → suc (inv w′) ≤ z) (sym (inv-move m))
                         (subst (_≤ (inv w′ + drop m)) (+-comm (inv w′) 1)
                                (lift p)))
                  (inv-moves back))
    where
    lift : ∀ {a n} → 1 ≤ n → a + 1 ≤ a + n
    lift {zero}  q = q
    lift {suc a} q = s≤s (lift q)

------------------------------------------------------------------------
-- Positions: why precedence gives Ok at every cut.

record Step : Set where
  constructor step
  field
    lo hi : Nat
    wf    : suc lo ≤ hi       -- a step acts on a nonempty interval
open Step

private
  ≤? : ∀ m n → Dec (m ≤ n)
  ≤? zero    n       = yes z≤n
  ≤? (suc m) zero    = no (λ ())
  ≤? (suc m) (suc n) with ≤? m n
  ... | yes p = yes (s≤s p)
  ... | no ¬p = no (λ { (s≤s p) → ¬p p })

  sideOf : ∀ {A : Set} → Dec A → Side
  sideOf (yes _) = L
  sideOf (no _)  = R

  sideOf-L : ∀ {A : Set} (d : Dec A) → sideOf d ≡ L → A
  sideOf-L (yes a) _ = a
  sideOf-L (no _)  ()

  sideOf-R : ∀ {A : Set} (d : Dec A) → sideOf d ≡ R → ¬ A
  sideOf-R (yes _) ()
  sideOf-R (no ¬a) _ = ¬a

-- The side of a step for the cut at h: L when it ends by h.
sideAt : Nat → Step → Side
sideAt h s = sideOf (≤? (hi s) h)

-- A step respects h when it lies wholly on one side.
Respects : Nat → Step → Set
Respects h s = (hi s ≤ h) ⊎ (h ≤ lo s)

-- If every step of U ends before every step of V starts, then at every
-- cut both respect, V has no L step paired with an R step of U.
precedes→ok : ∀ h (u v : Step) → hi u ≤ lo v → Respects h u →
              Cut.Ok (sideAt h) v u
precedes→ok h u v uv ru (vL , uR) with ru
... | inj₁ hu = sideOf-R (≤? (hi u) h) uR hu
... | inj₂ hl = suc≰ (≤-trans (≤-trans (s≤s hl) (wf u))
                      (≤-trans uv (≤-trans (≤-step ≤-refl′) (≤-trans (wf v) hv))))
  where
  hv : hi v ≤ h
  hv = sideOf-L (≤? (hi v) h) vL
  ≤-refl′ : lo v ≤ lo v
  ≤-refl′ = ≤-refl
