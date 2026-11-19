------------------------------------------------------------------------
-- Typing and subject reduction for N/β/η (D18).
--
-- A signature gives each generator a source and a target formula
-- (sources nonempty), and a residual factor H_a Z = hom d A Z for
-- each tag a = (d, A).  Typing is relational:
--
--   gen x       : src x → tgt x
--   e_{a,Z}     : T_a(H_a Z) → Z
--   κ_a(f)      : X → H_a Z      when f : T_a X → Z and X ≠ ∅
--   (L, q, R)   : L X R → L Y R  when q : X → Y
--
-- Subject reduction: if u : S → T and u ⟶ v then v : S → T.  With it,
-- the untyped confluence and decision results restrict to typed words:
-- every reduction from a typed word stays typed, so the typed steps are
-- exactly the untyped steps between typed words and the joins of
-- `Confluence` and `Decide` are typed.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Typing (Fac G : Set) where

open import CaTTExp.Gray.NBE.Base
open import CaTTExp.Gray.NBE.Syntax Fac G
open import CaTTExp.Gray.NBE.Lemmas Fac G
open import CaTTExp.Gray.NBE.Confluence Fac G

data NonEmpty : Formula → Set where
  ne : ∀ x xs → NonEmpty (x ∷ xs)

ne-mid : ∀ L {X} R → NonEmpty X → NonEmpty (L ++ X ++ R)
ne-mid []      R (ne x xs) = ne x (xs ++ R)
ne-mid (y ∷ L) R _         = ne y (L ++ _ ++ R)

-- P (L X R) Q ≡ (P L) X (R Q)
ctx-eq : ∀ (P L X R Q : Formula) → P ++ (L ++ X ++ R) ++ Q ≡ (P ++ L) ++ X ++ (R ++ Q)
ctx-eq P L X R Q =
  trans (cong (P ++_) (trans (++-assoc L (X ++ R) Q)
                             (cong (L ++_) (++-assoc X R Q))))
        (sym (++-assoc P L (X ++ (R ++ Q))))

cancel3 : ∀ (P : Formula) {A B : Formula} (Q : Formula) → P ++ A ++ Q ≡ P ++ B ++ Q → A ≡ B
cancel3 P {A} {B} Q e = ++-cancelʳ A B (++-cancelˡ P e)

module Typed
  (hom    : Dir → Formula → Formula → Fac)
  (src tgt : G → Formula)
  (src-ne : ∀ x → NonEmpty (src x))
  where

  Ta : Dir → Formula → Formula → Formula
  Ta d A X = pre d A ++ X ++ post d A

  Ha : Dir → Formula → Formula → Formula
  Ha d A Z = hom d A Z ∷ []

  mutual
    data TyP : Prim → Formula → Formula → Set where
      tgen : ∀ x → TyP (gen x) (src x) (tgt x)
      tev  : ∀ d A Z → TyP (ev d A Z) (Ta d A (Ha d A Z)) Z
      tcur : ∀ {d A Z b X} → NonEmpty X → Ty b (Ta d A X) Z
           → TyP (cur d A Z b) X (Ha d A Z)

    data TyT : Triple → Formula → Formula → Set where
      tyT : ∀ {l q r X Y S T} → TyP q X Y
          → S ≡ l ++ X ++ r → T ≡ l ++ Y ++ r → TyT (tri l q r) S T

    data Ty : Word → Formula → Formula → Set where
      tnil  : ∀ {S T} → S ≡ T → Ty [] S T
      tcons : ∀ {t w S M T} → TyT t S M → Ty w M T → Ty (t ∷ w) S T

  ------------------------------------------------------------------
  -- Structural typing lemmas

  ty-src : ∀ {w S S' T} → S ≡ S' → Ty w S' T → Ty w S T
  ty-src refl p = p

  ty-tgt : ∀ {w S T T'} → Ty w S T' → T' ≡ T → Ty w S T
  ty-tgt p refl = p

  tyP-ne : ∀ {q X Y} → TyP q X Y → NonEmpty X
  tyP-ne (tgen x)     = src-ne x
  tyP-ne (tev d A Z)  = ne-mid (pre d A) (post d A) (ne (hom d A Z) [])
  tyP-ne (tcur n _)   = n

  ty-++ : ∀ {xs ys S M T} → Ty xs S M → Ty ys M T → Ty (xs ++ ys) S T
  ty-++ (tnil refl)  q = q
  ty-++ (tcons t p)  q = tcons t (ty-++ p q)

  ty-split : ∀ xs {ys S T} → Ty (xs ++ ys) S T
    → Σ Formula λ M → Ty xs S M × Ty ys M T
  ty-split []       p           = _ , tnil refl , p
  ty-split (x ∷ xs) (tcons t p) with ty-split xs p
  ... | M , a , b = M , tcons t a , b

  ty-ctx : ∀ P Q {g S T} → Ty g S T → Ty (map (inCtx P Q) g) (P ++ S ++ Q) (P ++ T ++ Q)
  ty-ctx P Q (tnil e) = tnil (cong (λ k → P ++ k ++ Q) e)
  ty-ctx P Q (tcons (tyT {l = l} {r = r} {X = X} {Y = Y} p e f) rest) =
    tcons (tyT p (trans (cong (λ k → P ++ k ++ Q) e) (ctx-eq P l X r Q))
                 (trans (cong (λ k → P ++ k ++ Q) f) (ctx-eq P l Y r Q)))
          (ty-ctx P Q rest)

  ty-unctx : ∀ P Q g {S' T' S T} → Ty (map (inCtx P Q) g) S' T'
    → S' ≡ P ++ S ++ Q → T' ≡ P ++ T ++ Q → Ty g S T
  ty-unctx P Q [] (tnil e) e1 e2 =
    tnil (cancel3 P Q (trans (sym e1) (trans e e2)))
  ty-unctx P Q (tri l q r ∷ g) {S = S} (tcons (tyT {X = X} {Y = Y} p e f) rest) e1 e2 =
    tcons (tyT p (cancel3 P Q (trans (sym e1) (trans e (sym (ctx-eq P l X r Q))))) refl)
          (ty-unctx P Q g rest (trans f (sym (ctx-eq P l Y r Q))) e2)

  ------------------------------------------------------------------
  -- Subject reduction

  sr : ∀ {u v S T} → Ty u S T → u ⟶ v → Ty v S T
  -- N
  sr {S = S}
     (tcons (tyT {X = X0} {Y = Y0} p0 e0 f0)
            (tcons (tyT {X = X1} (tcur {d = d} {A = A} n tb) e1 f1) tw))
     (N {CL = CL} {CR = CR} {D0L = D0L} {D0R = D0R} refl refl) =
    tcons (tyT (tcur (ne-mid D0L D0R (tyP-ne p0))
                     (tcons (tyT p0 (ctx-eq (pre d A) D0L X0 D0R (post d A))
                                    (trans (cong (λ k → pre d A ++ k ++ post d A) eX1)
                                           (ctx-eq (pre d A) D0L Y0 D0R (post d A))))
                            tb))
               (trans e0 (sym (ctx-eq CL D0L X0 D0R CR)))
               f1)
          tw
    where
      eX1 : X1 ≡ D0L ++ Y0 ++ D0R
      eX1 = cancel3 CL CR (trans (sym e1) (trans f0 (sym (ctx-eq CL D0L Y0 D0R CR))))
  -- β
  sr (tcons (tyT {X = X} (tcur {d = d} {A = A} n tb) e1 f1)
            (tcons (tyT (tev _ _ _) e2 f2) tw))
     (β {CL = CL} {CR = CR} refl refl) =
    ty-++ (ty-src (trans e1 (sym (ctx-eq CL (pre d A) X (post d A) CR)))
                  (ty-ctx CL CR tb))
          (ty-src (sym f2) tw)
  -- η
  sr (tcons (tyT {X = X} (tcur {d = d} {A = A} {Z = Z} n tb) e1 f1) tw)
     (η {CL = CL} {CR = CR} {g = g} refl)
    with ty-split (map (wrap d A) g) tb
  ... | M , tg , tcons (tyT (tev _ _ _) e f) (tnil e') =
    ty-++ (ty-src e1 (ty-ctx CL CR
             (ty-unctx (pre d A) (post d A) g tg refl
                (trans e (++-identityʳ (Ta d A (Ha d A Z)))))))
          (ty-src (sym f1) tw)
  -- congruences
  sr (tcons t tw) (skip s) = tcons t (sr tw s)
  sr (tcons (tyT (tcur n tb) e f) tw) (body s) = tcons (tyT (tcur n (sr tb s)) e f) tw

  sr* : ∀ {u v S T} → Ty u S T → u ⟶* v → Ty v S T
  sr* p ε       = p
  sr* p (s ◅ q) = sr* (sr p s) q

  ------------------------------------------------------------------
  -- Typed corollaries

  -- Two typed reductions of a typed word are joined by a typed word.
  typed-confluence : ∀ {u v1 v2 S T} → Ty u S T → u ⟶* v1 → u ⟶* v2
    → Σ Word λ w → (v1 ⟶* w) × (v2 ⟶* w) × Ty w S T
  typed-confluence tu p q with confluence p q
  ... | w , a , b = w , a , b , sr* (sr* tu p) a
