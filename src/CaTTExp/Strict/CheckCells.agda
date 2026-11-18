------------------------------------------------------------------------
-- Checks by evaluation of (T-cell) of CaTTExp.Strict.Soundness.
--
-- A boolean checker cell? for IsCellL, proved sound (cell-sound), and
-- its evaluation on the total cell twT of 18 pasting contexts: points,
-- single homs ΣDⁿ (n ≤ 3), wedges of up to four ΣD¹, mixed dimensions,
-- wedges with a point factor, and homs that are themselves composites.
-- Tcell-inst turns each check into an IsCellL proof. The general
-- statement is proved in CaTTExp.Strict.Bridge (`T-cell`); these
-- checks are an independent test of it.
------------------------------------------------------------------------
module CaTTExp.Strict.CheckCells where


open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Soundness
open import CaTTExp.Gray.Pure hiding (Tuple)

------------------------------------------------------------------------
-- A sound boolean checker for IsCellL.

memB : Tuple → Bag → Bool
memB a []      = false
memB a (x ∷ X) = eqT a x ∨ memB a X

rmB : Tuple → Bag → Bag
rmB a []      = []
rmB a (x ∷ X) = if eqT a x then X else (x ∷ rmB a X)

perm? : Bag → Bag → Bool
perm? []      []      = true
perm? []      (_ ∷ _) = false
perm? (x ∷ X) Y       = memB x Y ∧ perm? X (rmB x Y)

private
  rm-≈ : ∀ a Y → T (memB a Y) → Y ≈ a ∷ rmB a Y
  rm-≈ a (y ∷ Y) m with eqT a y in e
  ... | true rewrite eqT-sound a y (subst T (sym e) tt) = ≈-refl
  ... | false =
    ≈-trans (++-cong (≈-refl {y ∷ []}) (rm-≈ a Y m))
            (++-cong (++-comm (y ∷ []) (a ∷ [])) (≈-refl {rmB a Y}))

perm-sound : ∀ X Y → T (perm? X Y) → X ≈ Y
perm-sound []      []      _ = ≈-refl
perm-sound (x ∷ X) Y       p =
  ≈-trans (++-cong (≈-refl {x ∷ []}) (perm-sound X (rmB x Y) (∧-snd {memB x Y} p)))
          (≈-sym (rm-≈ x Y (∧-fst p)))

wft? : Ctx → Nat → Nat → Tuple → Bool
wft? Γ x y []      = x ==ℕ y
wft? Γ x y (v ∷ w) with endsL (lookup Γ v)
... | nothing      = false
... | just (a , b) = (a ==ℕ x) ∧ wft? Γ b y w

wft-sound : ∀ Γ x y w → T (wft? Γ x y w) → WFT Γ x y w
wft-sound Γ x y []      p = ==ℕ-sound x y p
wft-sound Γ x y (v ∷ w) p with endsL (lookup Γ v) in e
... | just (a , b) =
  b , cong (λ q → just (q , b)) (==ℕ-sound a x (∧-fst p)) ,
  wft-sound Γ b y w (∧-snd {a ==ℕ x} p)

bas? : Ctx → Nat → Nat → Nat → Tuple → Bool
bas? Γ x y k w = wft? Γ x y w ∧ (deg Γ w ==ℕ k)

bas-sound : ∀ Γ x y k w → T (bas? Γ x y k w) → Basis Γ x y k w
bas-sound Γ x y k w p = wft-sound Γ x y w (∧-fst p) , ==ℕ-sound _ _ (∧-snd {wft? Γ x y w} p)

allB? : Ctx → Nat → Nat → Nat → Bag → Bool
allB? Γ x y k []      = true
allB? Γ x y k (w ∷ c) = bas? Γ x y k w ∧ allB? Γ x y k c

allB-sound : ∀ Γ x y k c → T (allB? Γ x y k c) → All (Basis Γ x y k) c
allB-sound Γ x y k []      _ = tt
allB-sound Γ x y k (w ∷ c) p = bas-sound Γ x y k w (∧-fst p) , allB-sound Γ x y k c (∧-snd {bas? Γ x y k w} p)

tweq? : Tower → Tower → Bool
tweq? (base c)     (base c')       = perm? c c'
tweq? (step S U c) (step S' U' c') = tweq? S S' ∧ tweq? U U' ∧ perm? c c'
tweq? _ _ = false

tweq-sound : ∀ X Y → T (tweq? X Y) → X ≈w Y
tweq-sound (base c) (base c') p = perm-sound c c' p
tweq-sound (step S U c) (step S' U' c') p =
  tweq-sound S S' (∧-fst p) , tweq-sound U U' (∧-fst (∧-snd {tweq? S S'} p)) ,
  perm-sound c c' (∧-snd {tweq? U U'} (∧-snd {tweq? S S'} p))

par? : Tower → Tower → Bool
par? (base _) (base _) = true
par? (step S U _) (step S' U' _) = tweq? S S' ∧ tweq? U U'
par? _ _ = false

par-sound : ∀ X Y → T (par? X Y) → Par X Y
par-sound (base _) (base _) _ = tt
par-sound (step S U _) (step S' U' _) p = tweq-sound S S' (∧-fst p) , tweq-sound U U' (∧-snd {tweq? S S'} p)

cell? : Ctx → Nat → Nat → Nat → Tower → Bool
cell? Γ x y zero    (base (w ∷ [])) = bas? Γ x y 0 w
cell? Γ x y (suc n) (step S U c) =
  cell? Γ x y n S ∧ cell? Γ x y n U ∧ par? S U ∧
  perm? (∂B Γ true c ++ top S) (∂B Γ false c ++ top U) ∧ allB? Γ x y (suc n) c
cell? _ _ _ _ _ = false

cell-sound : ∀ Γ x y n X → T (cell? Γ x y n X) → IsCellL Γ x y n X
cell-sound Γ x y zero (base (w ∷ [])) p = w , ≈-refl , bas-sound Γ x y 0 w p
cell-sound Γ x y (suc n) (step S U c) p =
  let p1 = ∧-fst p
      r1 = ∧-snd {cell? Γ x y n S} p
      p2 = ∧-fst r1
      r2 = ∧-snd {cell? Γ x y n U} r1
      p3 = ∧-fst r2
      r3 = ∧-snd {par? S U} r2
      p4 = ∧-fst r3
      p5 = ∧-snd {perm? (∂B Γ true c ++ top S) (∂B Γ false c ++ top U)} r3
  in cell-sound Γ x y n S p1 , cell-sound Γ x y n U p2 , par-sound S U p3 ,
     perm-sound _ _ p4 , allB-sound Γ x y (suc n) c p5

------------------------------------------------------------------------
-- T-cell instance checker: first and last object.

firstO lastO : List Nat → Nat
firstO []      = 0
firstO (x ∷ _) = x
lastO []           = 0
lastO (x ∷ [])     = x
lastO (_ ∷ y ∷ ys) = lastO (y ∷ ys)

Tcell? : Ctx → Bool
Tcell? Θ = cell? Θ (firstO (objs Θ)) (lastO (objs Θ)) (dimK (homs Θ)) (twT (homs Θ) true (dimK (homs Θ)))

Tcell-inst : ∀ Θ → T (Tcell? Θ) → IsCellL Θ (firstO (objs Θ)) (lastO (objs Θ)) (dimK (homs Θ)) (twT (homs Θ) true (dimK (homs Θ)))
Tcell-inst Θ p = cell-sound Θ _ _ _ _ p

------------------------------------------------------------------------
-- The checks.

l = leaf
d1 = node (l ∷ [])               -- D¹ as hom tree
d2 = node (d1 ∷ [])
d3 = node (d2 ∷ [])

S : List Tree → Ctx
S ts = ctxOf (node ts)

t-D0    = Tcell? (ctxOf leaf)
t-SD0   = Tcell? (S (l ∷ []))
t-SD1   = Tcell? (S (d1 ∷ []))
t-SD2   = Tcell? (S (d2 ∷ []))
t-SD3   = Tcell? (S (d3 ∷ []))
t-11    = Tcell? (S (d1 ∷ d1 ∷ []))
t-111   = Tcell? (S (d1 ∷ d1 ∷ d1 ∷ []))
t-21    = Tcell? (S (d2 ∷ d1 ∷ []))
t-12    = Tcell? (S (d1 ∷ d2 ∷ []))
t-22    = Tcell? (S (d2 ∷ d2 ∷ []))
t-101   = Tcell? (S (d1 ∷ l ∷ d1 ∷ []))
t-vc1   = Tcell? (S (node (l ∷ l ∷ []) ∷ d1 ∷ []))       -- hom: two composable 1-cells (dim 1) ⊗ D¹
t-hv    = Tcell? (S (node (d1 ∷ d1 ∷ []) ∷ d1 ∷ []))     -- hom: horizontal pair of 2-cells? (hd 2) ⊗ D¹
t-vv    = Tcell? (S (node (node (l ∷ l ∷ []) ∷ []) ∷ d1 ∷ []))  -- hom: vertical pair of 2-cells ⊗ D¹
t-mix   = Tcell? (S (node (d1 ∷ l ∷ []) ∷ node (l ∷ d1 ∷ []) ∷ []))
t-1111  = Tcell? (S (d1 ∷ d1 ∷ d1 ∷ d1 ∷ []))
t-31    = Tcell? (S (d3 ∷ d1 ∷ []))
t-big   = Tcell? (S (node (node (l ∷ l ∷ []) ∷ d1 ∷ []) ∷ node (d1 ∷ l ∷ []) ∷ []))

_ : t-D0 ≡ true
_ = refl
_ : t-SD0 ≡ true
_ = refl
_ : t-SD1 ≡ true
_ = refl
_ : t-SD2 ≡ true
_ = refl
_ : t-SD3 ≡ true
_ = refl
_ : t-11 ≡ true
_ = refl
_ : t-111 ≡ true
_ = refl
_ : t-21 ≡ true
_ = refl
_ : t-12 ≡ true
_ = refl
_ : t-22 ≡ true
_ = refl
_ : t-101 ≡ true
_ = refl
_ : t-vc1 ≡ true
_ = refl
_ : t-hv ≡ true
_ = refl
_ : t-vv ≡ true
_ = refl
_ : t-mix ≡ true
_ = refl
_ : t-1111 ≡ true
_ = refl
_ : t-31 ≡ true
_ = refl
_ : t-big ≡ true
_ = refl

-- concrete instance as an actual IsCellL proof
inst-111 = Tcell-inst (S (d1 ∷ d1 ∷ d1 ∷ [])) tt
inst-21  = Tcell-inst (S (d2 ∷ d1 ∷ [])) tt
