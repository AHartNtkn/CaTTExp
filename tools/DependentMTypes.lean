import Std

/-! A rectangular band has a multiplication that keeps the left coordinate
of its first argument and the right coordinate of its second argument.
The transition in a dialgebra below is defined exactly on its pullback. -/
namespace Rect

structure Band where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  idem : ∀ x, mul x x = x
  left : ∀ x y z, mul (mul x y) z = mul x z
  right : ∀ x y z, mul x (mul y z) = mul x z

def grid (L R : Type) : Band where
  Carrier := L × R
  mul x y := (x.1, y.2)
  idem _ := rfl
  left _ _ _ := rfl
  right _ _ _ := rfl

structure Map (B C : Band) where
  fn : B.Carrier → C.Carrier
  mul : ∀ x y, fn (B.mul x y) = C.mul (fn x) (fn y)

def Map.comp {A B C : Band} (g : Map B C) (f : Map A B) : Map A C where
  fn x := g.fn (f.fn x)
  mul x y := by rw [f.mul, g.mul]

def Map.id (B : Band) : Map B B := ⟨fun x => x, fun _ _ => rfl⟩
def Map.const {B C : Band} (z : C.Carrier) : Map B C :=
  ⟨fun _ => z, fun _ _ => (C.idem z).symm⟩

def unit := grid Unit Unit

structure Dial {E A : Band} (p : Map E A) where
  C : Band
  h : Map C A
  t : (c : C.Carrier) → (e : E.Carrier) → h.fn c = p.fn e → C.Carrier
  tmul : ∀ c d e f (ce : h.fn c = p.fn e) (df : h.fn d = p.fn f),
    t (C.mul c d) (E.mul e f) (by rw [h.mul, p.mul, ce, df]) =
    C.mul (t c e ce) (t d f df)

structure Hom {E A : Band} {p : Map E A} (D T : Dial p) where
  map : Map D.C T.C
  root : ∀ c, T.h.fn (map.fn c) = D.h.fn c
  step : ∀ c e (w : D.h.fn c = p.fn e),
    map.fn (D.t c e w) = T.t (map.fn c) e ((root c).trans w)

def Hom.comp {E A : Band} {p : Map E A} {D T V : Dial p}
    (g : Hom T V) (f : Hom D T) : Hom D V where
  map := g.map.comp f.map
  root c := (g.root _).trans (f.root c)
  step c e w := by
    change g.map.fn (f.map.fn (D.t c e w)) = _
    rw [f.step, g.step]
    rfl

def IsTerminal {E A : Band} {p : Map E A} (T : Dial p) :=
  ∀ D : Dial p, ∃ f : Hom D T, ∀ g : Hom D T, g.map.fn = f.map.fn

def constantStep {E A : Band} (p : Map E A) (a : A.Carrier) : Dial p where
  C := A
  h := Map.id A
  t _ _ _ := a
  tmul _ _ _ _ _ _ := (A.idem a).symm

def inactive {E A : Band} (p : Map E A) (a : A.Carrier)
    (off : ∀ e, a ≠ p.fn e) : Dial p where
  C := unit
  h := Map.const a
  t _ e w := False.elim (off e w)
  tmul _ _ e _ w _ := False.elim (off e w)

def incl {E A : Band} (p : Map E A) (a z : A.Carrier)
    (off : ∀ e, a ≠ p.fn e) : Hom (inactive p a off) (constantStep p z) where
  map := Map.const a
  root _ := rfl
  step _ e w := False.elim (off e w)

def boolBand := grid Bool Bool
def first : Map unit boolBand := Map.const (false, false)

def FinPos := (n : Nat) × Fin n
def natBand := grid Nat Nat
def finBand := grid FinPos FinPos
def finShape : Map finBand natBand where
  fn e := (e.1.1, e.2.1)
  mul _ _ := rfl

/-- Two labels with empty fibres generate a label admitting a transition.
Comparing constant transitions with distinct outputs precludes finality. -/
theorem inactiveProduct {E A : Band} (p : Map E A) (x y : A.Carrier)
    (offX : ∀ e, x ≠ p.fn e) (offY : ∀ e, y ≠ p.fn e)
    (e : E.Carrier) (onXY : A.mul x y = p.fn e)
    (a b : A.Carrier) (different : a ≠ b) : ¬ ∃ T : Dial p, IsTerminal T := by
  rintro ⟨T, terminal⟩
  obtain ⟨f, _⟩ := terminal (constantStep p a)
  obtain ⟨g, _⟩ := terminal (constantStep p b)
  have agree (z : A.Carrier) (off : ∀ d, z ≠ p.fn d) :
      f.map.fn z = g.map.fn z := by
    obtain ⟨k, unique⟩ := terminal (inactive p z off)
    have u := unique (f.comp (incl p z a off))
    have v := unique (g.comp (incl p z b off))
    exact congrFun (u.trans v.symm) ((), ())
  have same : f.map.fn (A.mul x y) = g.map.fn (A.mul x y) := by
    exact (f.map.mul x y).trans (Eq.trans
      (congrArg (fun z => T.C.mul z (f.map.fn y)) (agree x offX))
      (Eq.trans (congrArg (fun z => T.C.mul (g.map.fn x) z) (agree y offY))
        (g.map.mul x y).symm))
  have transport (i j : T.C.Carrier) (h : i = j)
      (hi : T.h.fn i = p.fn e) (hj : T.h.fn j = p.fn e) :
      T.t i e hi = T.t j e hj := by
    subst j
    rfl
  have next : f.map.fn a = g.map.fn b :=
    (f.step (A.mul x y) e onXY).trans
      ((transport _ _ same _ _).trans (g.step (A.mul x y) e onXY).symm)
  exact different ((f.root a).symm.trans ((congrArg T.h.fn next).trans (g.root b)))

theorem noFirst : ¬ ∃ T : Dial first, IsTerminal T := by
  apply inactiveProduct first (false, true) (true, false)
    (fun _ => by intro h; cases h) (fun _ => by intro h; cases h) ((), ()) rfl
    (false, false) (true, true) (by intro h; cases h)

theorem noFin : ¬ ∃ T : Dial finShape, IsTerminal T := by
  apply inactiveProduct finShape (1, 0) (0, 1) _ _
    (⟨1, 0⟩, ⟨1, 0⟩) rfl (0, 0) (1, 1) (by intro h; cases h)
  · intro e h
    have hz : 0 = e.2.1 := congrArg Prod.snd h
    exact Fin.elim0 (hz.symm ▸ e.2.2)
  · intro e h
    have hz : 0 = e.1.1 := congrArg Prod.fst h
    exact Fin.elim0 (hz.symm ▸ e.1.2)

#print axioms inactiveProduct
#print axioms noFirst
#print axioms noFin

end Rect
