------------------------------------------------------------------------
-- Structural lemmas for the N/β/η step relation (D18): closure of
-- steps under the word and context operations, the iterated
-- naturality rule N*, and reflection of steps through a tensor
-- context and through a trailing evaluation.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Lemmas (Fac G : Set) where

open import CaTTExp.Gray.NBE.Base
open import CaTTExp.Gray.NBE.Syntax Fac G

------------------------------------------------------------------------
-- Equality plumbing

step≡ : ∀ {u v v'} → u ⟶ v → v ≡ v' → u ⟶ v'
step≡ s refl = s

≡* : ∀ {u v} → u ≡ v → u ⟶* v
≡* refl = ε

one : ∀ {u v} → u ⟶ v → u ⟶* v
one s = s ◅ ε

------------------------------------------------------------------------
-- Contexts

tri-l : Triple → Formula
tri-l (tri l _ _) = l

tri-q : Triple → Prim
tri-q (tri _ q _) = q

tri-r : Triple → Formula
tri-r (tri _ _ r) = r

inCtx-∘ : ∀ P S P' S' t → inCtx P S (inCtx P' S' t) ≡ inCtx (P ++ P') (S' ++ S) t
inCtx-∘ P S P' S' (tri l q r) =
  cong₂ (λ a c → tri a q c) (sym (++-assoc P P' l)) (++-assoc r S' S)

map-inCtx-∘ : ∀ P S P' S' g
  → map (inCtx P S) (map (inCtx P' S') g) ≡ map (inCtx (P ++ P') (S' ++ S)) g
map-inCtx-∘ P S P' S' g =
  trans (map-∘ (inCtx P S) (inCtx P' S') g) (map-ext (inCtx-∘ P S P' S') g)

inCtx-[] : ∀ t → inCtx [] [] t ≡ t
inCtx-[] (tri l q r) = cong (tri l q) (++-identityʳ r)

inCtx-inj : ∀ P S {t t'} → inCtx P S t ≡ inCtx P S t' → t ≡ t'
inCtx-inj P S {tri l q r} {tri l' q' r'} e =
  cong₂ (λ a (bc : Prim × Formula) → tri a (fst bc) (snd bc))
        (++-cancelˡ P (cong tri-l e))
        (cong₂ _,_ (cong tri-q e) (++-cancelʳ r r' (cong tri-r e)))

map-inj : ∀ {A B : Set} (h : A → B) → (∀ {x y} → h x ≡ h y → x ≡ y)
  → ∀ xs ys → map h xs ≡ map h ys → xs ≡ ys
map-inj h inj []       []       e = refl
map-inj h inj []       (y ∷ ys) ()
map-inj h inj (x ∷ xs) []       ()
map-inj h inj (x ∷ xs) (y ∷ ys) e =
  cong₂ _∷_ (inj (∷-injˡ e)) (map-inj h inj xs ys (∷-injʳ e))

-- If map h g ends in y, then g ends in some t with h t ≡ y.
map-snoc : ∀ {A B : Set} (h : A → B) g xs y → map h g ≡ xs ++ (y ∷ [])
  → Σ (List A) λ g0 → Σ A λ t →
      (g ≡ g0 ++ (t ∷ [])) × (xs ≡ map h g0) × (h t ≡ y)
map-snoc h []      []       y ()
map-snoc h []      (x ∷ xs) y ()
map-snoc h (t ∷ []) [] y e = [] , t , refl , refl , ∷-injˡ e
map-snoc h (t ∷ (t' ∷ g)) [] y ()
map-snoc h (t ∷ g) (x ∷ xs) y e with map-snoc h g xs y (∷-injʳ e)
... | g0 , t' , e1 , e2 , e3 =
  t ∷ g0 , t' , cong (t ∷_) e1 , cong₂ _∷_ (sym (∷-injˡ e)) e2 , e3

------------------------------------------------------------------------
-- Closure of steps

no-step-[] : ∀ {v} → [] ⟶ v → ⊥
no-step-[] ()

skip* : ∀ {t w w'} → w ⟶* w' → t ∷ w ⟶* t ∷ w'
skip* ε       = ε
skip* (s ◅ p) = skip s ◅ skip* p

body* : ∀ {l r d A Z b b' w} → b ⟶* b'
  → tri l (cur d A Z b) r ∷ w ⟶* tri l (cur d A Z b') r ∷ w
body* ε       = ε
body* (s ◅ p) = body s ◅ body* p

pre⟶ : ∀ z {w w'} → w ⟶ w' → z ++ w ⟶ z ++ w'
pre⟶ []      s = s
pre⟶ (t ∷ z) s = skip (pre⟶ z s)

suf⟶ : ∀ z {w w'} → w ⟶ w' → w ++ z ⟶ w' ++ z
suf⟶ z (N e f) = N e f
suf⟶ z (β {CL = CL} {CR = CR} {b = b} {w = w} e f) =
  step≡ (β e f) (sym (++-assoc (map (inCtx CL CR) b) w z))
suf⟶ z (η {CL = CL} {CR = CR} {g = g} {w = w} p) =
  step≡ (η p) (sym (++-assoc (map (inCtx CL CR) g) w z))
suf⟶ z (skip s) = skip (suf⟶ z s)
suf⟶ z (body s) = body s

suf* : ∀ z {w w'} → w ⟶* w' → w ++ z ⟶* w' ++ z
suf* z ε       = ε
suf* z (s ◅ p) = suf⟶ z s ◅ suf* z p

ctx⟶ : ∀ P S {w w'} → w ⟶ w' → map (inCtx P S) w ⟶ map (inCtx P S) w'
ctx⟶ P S (N {CL = CL} {CR = CR} {D0L = D0L} {D0R = D0R} e f) =
  N (trans (cong (P ++_) e) (sym (++-assoc P CL D0L)))
    (trans (cong (_++ S) f) (++-assoc D0R CR S))
ctx⟶ P S (β {CL = CL} {CR = CR} {d = d} {A = A} {b = b} {w = w} e f) =
  step≡ (β (trans (cong (P ++_) e) (sym (++-assoc P CL (pre d A))))
           (trans (cong (_++ S) f) (++-assoc (post d A) CR S)))
        (sym (trans (map-++ (inCtx P S) (map (inCtx CL CR) b) w)
                    (cong (_++ map (inCtx P S) w) (map-inCtx-∘ P S CL CR b))))
ctx⟶ P S (η {CL = CL} {CR = CR} {g = g} {w = w} p) =
  step≡ (η p)
        (sym (trans (map-++ (inCtx P S) (map (inCtx CL CR) g) w)
                    (cong (_++ map (inCtx P S) w) (map-inCtx-∘ P S CL CR g))))
ctx⟶ P S (skip s) = skip (ctx⟶ P S s)
ctx⟶ P S (body s) = body s

------------------------------------------------------------------------
-- Iterated naturality N*:  C[h] ; C[κ_a(f)]  ⟶*  C[κ_a(T_a[h] ; f)]

N* : ∀ {CL CR d A Z b w} h
  → map (inCtx CL CR) h ++ (tri CL (cur d A Z b) CR ∷ w)
    ⟶* tri CL (cur d A Z (map (wrap d A) h ++ b)) CR ∷ w
N* []              = ε
N* (tri l q r ∷ h) = skip* (N* h) ◅◅ one (N refl refl)

------------------------------------------------------------------------
-- Reflection of a step through a tensor context

Refl : Formula → Formula → Word → Word → Set
Refl P S g v = Σ Word λ g' → (g ⟶ g') × (v ≡ map (inCtx P S) g')

ctx-refl : ∀ P S g {v} → map (inCtx P S) g ⟶ v → Refl P S g v
ctx-refl P S [] ()
ctx-refl P S (tri l q r ∷ []) (η {CL = .(P ++ l)} {CR = .(r ++ S)} {g = g} p) =
  map (inCtx l r) g ++ [] , η p ,
  trans (cong (_++ []) (sym (map-inCtx-∘ P S l r g)))
        (sym (map-++ (inCtx P S) (map (inCtx l r) g) []))
ctx-refl P S (tri l q r ∷ []) (skip ())
ctx-refl P S (tri l q r ∷ []) (body s) = _ , body s , refl
ctx-refl P S (tri l1 q1 r1 ∷ tri l2 q2 r2 ∷ g) (N {D0L = D0L} {D0R = D0R} e f) =
  _ ,
  N (++-cancelˡ P (trans e (++-assoc P l2 D0L)))
    (++-cancelʳ r1 (D0R ++ r2) (trans f (sym (++-assoc D0R r2 S)))) ,
  refl
ctx-refl P S (tri l1 q1 r1 ∷ tri l2 q2 r2 ∷ g) (β {d = d} {A = A} {b = b} e f) =
  map (inCtx l2 r2) b ++ g ,
  β (++-cancelˡ P (trans e (++-assoc P l2 (pre d A))))
    (++-cancelʳ r1 (post d A ++ r2) (trans f (sym (++-assoc (post d A) r2 S)))) ,
  trans (cong (_++ map (inCtx P S) g) (sym (map-inCtx-∘ P S l2 r2 b)))
        (sym (map-++ (inCtx P S) (map (inCtx l2 r2) b) g))
ctx-refl P S (tri l1 q1 r1 ∷ t2 ∷ g) (η {g = g0} p) =
  map (inCtx l1 r1) g0 ++ t2 ∷ g , η p ,
  trans (cong (_++ map (inCtx P S) (t2 ∷ g)) (sym (map-inCtx-∘ P S l1 r1 g0)))
        (sym (map-++ (inCtx P S) (map (inCtx l1 r1) g0) (t2 ∷ g)))
ctx-refl P S (t1 ∷ t2 ∷ g) (skip s) with ctx-refl P S (t2 ∷ g) s
... | g' , s' , e = t1 ∷ g' , skip s' , cong (inCtx P S t1 ∷_) e
ctx-refl P S (tri l1 q1 r1 ∷ t2 ∷ g) (body s) = _ , body s , refl

------------------------------------------------------------------------
-- A step on a word ending in an evaluation either happens before the
-- evaluation or is a β-redex that consumes it.

data EvSplit (xs : Word) (d : Dir) (A Z : Formula) (v : Word) : Set where
  before : ∀ xs' → xs ⟶ xs' → v ≡ xs' ++ (evT d A Z ∷ []) → EvSplit xs d A Z v
  beta   : ∀ xs0 f l r → xs ≡ xs0 ++ (tri l (cur d A Z f) r ∷ [])
         → l ≡ pre d A → r ≡ post d A ++ []
         → v ≡ xs0 ++ (map (inCtx [] []) f ++ [])
         → EvSplit xs d A Z v

ev-split : ∀ xs {d A Z v} → xs ++ (evT d A Z ∷ []) ⟶ v → EvSplit xs d A Z v
ev-split [] (skip ())
ev-split (t ∷ []) (β {b = b} e f) = beta [] b _ _ refl e f refl
ev-split (t ∷ []) {d} {A} {Z} (η {CL = CL} {CR = CR} {g = g} p) =
  before (map (inCtx CL CR) g ++ []) (η p)
         (cong (_++ (evT d A Z ∷ [])) (sym (++-identityʳ (map (inCtx CL CR) g))))
ev-split (t ∷ []) (skip (skip ()))
ev-split (t ∷ []) (body s) = before _ (body s) refl
ev-split (t1 ∷ t2 ∷ xs) (N e f) = before _ (N e f) refl
ev-split (t1 ∷ t2 ∷ xs) {d} {A} {Z} (β {CL = CL} {CR = CR} {b = b} e f) =
  before _ (β e f) (sym (++-assoc (map (inCtx CL CR) b) xs (evT d A Z ∷ [])))
ev-split (t1 ∷ t2 ∷ xs) {d} {A} {Z} (η {CL = CL} {CR = CR} {g = g} p) =
  before _ (η p) (sym (++-assoc (map (inCtx CL CR) g) (t2 ∷ xs) (evT d A Z ∷ [])))
ev-split (t1 ∷ t2 ∷ xs) (body s) = before _ (body s) refl
ev-split (t1 ∷ t2 ∷ xs) (skip s) with ev-split (t2 ∷ xs) s
... | before xs' s' e = before (t1 ∷ xs') (skip s') (cong (t1 ∷_) e)
... | beta xs0 f l r e1 e2 e3 e4 =
  beta (t1 ∷ xs0) f l r (cong (t1 ∷_) e1) e2 e3 (cong (t1 ∷_) e4)
