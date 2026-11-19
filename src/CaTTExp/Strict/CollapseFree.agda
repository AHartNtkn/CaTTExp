------------------------------------------------------------------------
-- The collapsed Gray cylinder is ν(Σ λD) (ledger A5, (N3), collapse
-- step 6).
--
-- For an ordered globular presentation D, the collapse
-- q : λD ⊗ λD¹ → Σ λD (`Collapse`) sends the end atoms ⟨k⊗0⟩, ⟨k⊗1⟩
-- to the points ⟨⊥⟩, ⟨⊤⟩ (`CollapseEnds.atom-end`) and ⟨k⊗i⟩ to ⟨Σk⟩
-- (`CollapseAtoms.atom-mid`). Let F : ν(λD ⊗ λD¹) → 𝒟 be a strict
-- functor that sends every ⟨k⊗0⟩ to one point p₀ and every ⟨k⊗1⟩ to
-- one point p₁ (`Corr.EndsAt`). Then F = G ∘ ν(q) for a strict functor
-- G : ν(Σ λD) → 𝒟 (`Corr.Exists.exists`), and G is unique once D has a
-- generator (`Corr.unique`). Conversely, G ∘ ν(q) sends the ends to
-- G⟨⊥⟩ and G⟨⊤⟩ (`Corr.ends-of`). So ν(Σ λD) is the quotient of
-- ν(λD ⊗ λD¹) by its two ends, as strict ω-categories.
--
-- The key step is `Bd`: for such an F and k of degree m ≥ 1 the
-- boundaries of F⟨k⊗i⟩ are F⟨sk⊗i⟩ and F⟨tk⊗i⟩. The (m)-source of
-- ⟨k⊗i⟩ has top row sk⊗i + k⊗e, so it splits as ⟨sk⊗i⟩ #ₘ₋₁ z with z
-- above m − 1 on the end k⊗e (`Split`); F flattens z (`Kill`), and the
-- composite with an identity is F⟨sk⊗i⟩.
------------------------------------------------------------------------
module CaTTExp.Strict.CollapseFree where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms using (at; unit; module Atom)
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Cylinder
open import CaTTExp.Strict.GlobBasis
open import CaTTExp.Strict.NuMap
open import CaTTExp.Strict.GlobAtoms
open import CaTTExp.Strict.Collapse
open import CaTTExp.Strict.Bag using (+-zero)
open import CaTTExp.Strict.Generation using (module Gen; ≤-dec; at0; at-0c)
open import CaTTExp.Strict.NuRows using (module Rows)
open import CaTTExp.Strict.Split
open import CaTTExp.Strict.Kill
open import CaTTExp.Strict.CylSplit
open import CaTTExp.Strict.Expr using (Functor)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

private
  <ℕ-sound′ : ∀ m n → (m <ℕ n) ≡ true → m < n
  <ℕ-sound′ zero    (suc n) e = s≤s z≤n
  <ℕ-sound′ (suc m) (suc n) e = s≤s (<ℕ-sound′ m n e)
  <ℕ-sound′ zero    zero    ()
  <ℕ-sound′ (suc m) zero    ()

  ∸-le : ∀ g j → g ∸ j ≤ g
  ∸-le zero    zero    = z≤n
  ∸-le zero    (suc j) = z≤n
  ∸-le (suc g) zero    = ≤-refl _
  ∸-le (suc g) (suc j) = ≤-suc (∸-le g j)

  ∸-sucl : ∀ g x → x ≤ g → suc g ∸ x ≡ suc (g ∸ x)
  ∸-sucl g       zero    _       = refl
  ∸-sucl (suc g) (suc x) (s≤s l) = ∸-sucl g x l

  ∸-∸ : ∀ g m → m ≤ g → g ∸ (g ∸ m) ≡ m
  ∸-∸ zero    zero    _       = refl
  ∸-∸ (suc g) zero    _       = ∸-∸′ g
    where
    ∸-∸′ : ∀ g → g ∸ g ≡ 0
    ∸-∸′ zero    = refl
    ∸-∸′ (suc g) = ∸-∸′ g
  ∸-∸ (suc g) (suc m) (s≤s l) = trans (∸-sucl g (g ∸ m) (∸-le g m)) (cong suc (∸-∸ g m l))

------------------------------------------------------------------------
-- ν(q) on the end atoms.

-- Offset of the copy k⊗e (e = true for the end 0) in the block of k.
off : Bool → Bool → Nat
off true  true  = 0
off false false = 0
off true  false = 2
off false true  = 2

module CollapseEnds (D : GData) where
  open GData D
  open Collapse D
  open Aux
  private
    module K  = GB D
    module S  = GB (Σg D)
    module GK = GA D
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    module AK = Atom K.basis
    module AS = Atom S.basis
  open Basis K.basis
  open Cyl K.basis

  -- The position of k⊗0 (b = true) or k⊗1 (b = false) in the layout.
  o : Bool → Nat → Nat
  o b k = k * 3 + off b (even (gd k))

  -- The point it goes to: ⊥ = 0 or ⊤ = N + 1 in Σ D.
  ib : Bool → Nat
  ib true  = 0
  ib false = suc N

  private
    XZ : Bool → Vec (Chn NS) N
    XZ true  = X
    XZ false = Z

    eb : Bool → Chn NS
    eb true  = e⊥
    eb false = e⊤

    lin-H : ∀ b v → lin (CD.Hc b v) Q ≡ lin v (XZ b)
    lin-H true  v = lin-c0 v
    lin-H false v = lin-c1 v

    lin-XZ : ∀ b p → p < N → lin (unit p) (XZ b) ≡ end (eb b) (gd p)
    lin-XZ true  = lin-X
    lin-XZ false = lin-Z

    o-lt : ∀ b k → k < N → off b (even (gd k)) < 3
    o-lt b k _ = go b (even (gd k))
      where
      go : ∀ b c → off b c < 3
      go true  true  = s≤s z≤n
      go false false = s≤s z≤n
      go true  false = s≤s (s≤s (s≤s z≤n))
      go false true  = s≤s (s≤s (s≤s z≤n))

  u-o : ∀ b k → k < N → unit (o b k) ≡ CD.Hc b (unit k)
  u-o b k kN rewrite sym (gk k kN) = go b (even (g k)) refl
    where
    LO HI : Bool → Set
    LO c = cyl gdeg (if c then unit k else 0c) 0c (if not c then unit k else 0c) ≡ unit (k * 3)
    HI c = cyl gdeg (if not c then unit k else 0c) 0c (if c then unit k else 0c) ≡ unit (k * 3 + 2)
    go : ∀ b c → even (g k) ≡ c → unit (k * 3 + off b c) ≡ CD.Hc b (unit k)
    go true  true  e = trans (cong unit (+-zero (k * 3))) (sym (subst LO e (cyl-unit-lo gdeg k kN)))
    go false false e = trans (cong unit (+-zero (k * 3))) (sym (subst LO e (cyl-unit-lo gdeg k kN)))
    go true  false e = sym (subst HI e (cyl-unit-hi gdeg k kN))
    go false true  e = sym (subst HI e (cyl-unit-hi gdeg k kN))

  deg-o : ∀ b k → k < N → CD.A′.deg (o b k) ≡ gd k
  deg-o b k kN =
    trans (at-cylA 0 gdeg gdeg (mapV suc gdeg) gdeg k (off b (even (gd k))) kN (o-lt b k kN))
      (trans (go b (even (gd k)) (even (at 0 gdeg k))) (gk k kN))
    where
    go : ∀ b c c′ → slot c′ (off b c) (g k) (at 0 (mapV suc gdeg) k) (g k) ≡ g k
    go true  true  true  = refl
    go true  true  false = refl
    go false false true  = refl
    go false false false = refl
    go true  false true  = refl
    go true  false false = refl
    go false true  true  = refl
    go false true  false = refl

  o-N : ∀ b k → k < N → o b k < N * 3
  o-N b k kN = go (o-lt b k kN)
    where
    go : ∀ {r} → r < 3 → k * 3 + r < N * 3
    go {r} l = ≤-trans (+-mono (k * 3) l) (*3-le kN)
      where
      +-mono : ∀ a {r} → r < 3 → suc (a + r) ≤ a + 3
      +-mono zero    l       = l
      +-mono (suc a) l       = s≤s (+-mono a l)
      *3-le : ∀ {k N} → k < N → k * 3 + 3 ≤ N * 3
      *3-le {zero}  {suc N} _       = s≤s (s≤s (s≤s z≤n))
      *3-le {suc k} {suc N} (s≤s l) = s≤s (s≤s (s≤s (*3-le l)))

  -- The rows of ⟨k⊗e⟩ under q: the point in degree 0, nothing above.
  private
    row-end : ∀ b k (kN : k < N) d → d ≤ gd k →
              (lin (fst (CD.A′.entK (o b k) d)) Q , lin (snd (CD.A′.entK (o b k) d)) Q)
              ≡ (end (eb b) (gd k ∸ d) , end (eb b) (gd k ∸ d))
    row-end b k kN d l =
      trans (cong (λ r → (lin (fst r) Q , lin (snd r) Q)) (CD.entK-end b (o b k) k (u-o b k kN) d))
        (cong₂ _,_
          (trans (lin-H b _) (trans (cong (λ v → lin v (XZ b)) (cong fst (GK.entK-glob d k kN l)))
            (trans (lin-XZ b _ (fst sok)) (cong (end (eb b)) (snd sok)))))
          (trans (lin-H b _) (trans (cong (λ v → lin v (XZ b)) (cong snd (GK.entK-glob d k kN l)))
            (trans (lin-XZ b _ (fst tok)) (cong (end (eb b)) (snd tok))))))
      where
      sok = GK.iter-ok s sN ds d k kN l
      tok = GK.iter-ok t tN dt d k kN l

    deg-ib : ∀ b → AS.deg (ib b) ≡ 0
    deg-ib true  = gΣ0
    deg-ib false = gΣ⊤

  ent-end : ∀ b k (kN : k < N) j →
            (lin (fst (CD.A′.ent (o b k) j)) Q , lin (snd (CD.A′.ent (o b k) j)) Q) ≡ AS.ent (ib b) j
  ent-end b k kN j = go (CD.A′.deg (o b k)) (AS.deg (ib b)) (deg-o b k kN) (deg-ib b) j
    where
    go : ∀ n n′ → n ≡ gd k → n′ ≡ 0 → ∀ j →
         (lin (fst (if j <ℕ suc n then CD.A′.entK (o b k) (n ∸ j) else (0c , 0c))) Q ,
          lin (snd (if j <ℕ suc n then CD.A′.entK (o b k) (n ∸ j) else (0c , 0c))) Q)
         ≡ (if j <ℕ suc n′ then AS.entK (ib b) (n′ ∸ j) else (0c , 0c))
    go n n′ refl refl zero =
      trans (row-end b k kN (gd k) (≤-refl _)) (trans (cong (λ h → (end (eb b) h , end (eb b) h)) (∸-∸ (gd k) 0 z≤n)) (e0 b))
      where
      e0 : ∀ b → (end (eb b) 0 , end (eb b) 0) ≡ AS.entK (ib b) 0
      e0 true  = refl
      e0 false = refl
    go n n′ refl refl (suc j) with j <ℕ gd k in e
    ... | true  =
      trans (row-end b k kN (gd k ∸ suc j) (∸-le (gd k) (suc j)))
        (cong (λ h → (end (eb b) h , end (eb b) h)) (∸-∸ (gd k) (suc j) (<ℕ-sound′ j (gd k) e)))
    ... | false = cong₂ _,_ (lin-0 Q) (lin-0 Q)

  private
    mapT-tabF : ∀ L′ {m} (f : Nat → Vec Nat (N * 3) × Vec Nat (N * 3)) j →
                mapT q L′ (Atom.tabF B′ {m} f j) ≡ Atom.tabF S.basis {m} (λ i → lin (fst (f i)) Q , lin (snd (f i)) Q) j
    mapT-tabF L′ {zero}  f j = refl
    mapT-tabF L′ {suc m} f j = cong (_ ∷_) (mapT-tabF L′ {m} f (suc j))

    tabF-cong : ∀ {m} (f g : Nat → Chn NS × Chn NS) → (∀ i → f i ≡ g i) → ∀ j →
                Atom.tabF S.basis {m} f j ≡ Atom.tabF S.basis {m} g j
    tabF-cong {zero}  f g h j = refl
    tabF-cong {suc m} f g h j = cong₂ _∷_ (h j) (tabF-cong {m} f g h (suc j))

  -- ν(q)⟨k⊗0⟩ = ⟨⊥⟩ and ν(q)⟨k⊗1⟩ = ⟨⊤⟩, as tables.
  atom-end : ∀ L b k → k < N → mapT q L (Atom.atomT B′ L (o b k)) ≡ Atom.atomT S.basis L (ib b)
  atom-end L b k kN = trans (mapT-tabF L (CD.A′.ent (o b k)) 0) (tabF-cong _ _ (ent-end b k kN) 0)

------------------------------------------------------------------------
-- The end generators k⊗0, k⊗1 of the cylinder, as a ∂-closed set.

private
  slot-F : ∀ {A : Set} c r → r < 3 → slot c r true false true ≡ false → (x y z : A) → slot c r x y z ≡ y
  slot-F true  zero                _ ()
  slot-F true  (suc zero)          _ _ x y z = refl
  slot-F true  (suc (suc zero))    _ ()
  slot-F false zero                _ ()
  slot-F false (suc zero)          _ _ x y z = refl
  slot-F false (suc (suc zero))    _ ()
  slot-F c     (suc (suc (suc r))) (s≤s (s≤s (s≤s ())))

  slot-T : ∀ {A : Set} (P : A → Set) c r → r < 3 → slot c r true false true ≡ true → ∀ x y z → P x → P z → P (slot c r x y z)
  slot-T P true  zero                _ _ x y z px pz = px
  slot-T P true  (suc zero)          _ ()
  slot-T P true  (suc (suc zero))    _ _ x y z px pz = pz
  slot-T P false zero                _ _ x y z px pz = pz
  slot-T P false (suc zero)          _ ()
  slot-T P false (suc (suc zero))    _ _ x y z px pz = px
  slot-T P c     (suc (suc (suc r))) (s≤s (s≤s (s≤s ())))

  slot-off : ∀ c r → r < 3 → slot c r true false true ≡ true → Σ Bool (λ b → r ≡ off b c)
  slot-off true  zero                _ _ = true , refl
  slot-off true  (suc zero)          _ ()
  slot-off true  (suc (suc zero))    _ _ = false , refl
  slot-off false zero                _ _ = false , refl
  slot-off false (suc zero)          _ ()
  slot-off false (suc (suc zero))    _ _ = true , refl
  slot-off c     (suc (suc (suc r))) (s≤s (s≤s (s≤s ())))

  at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
  at-out d []       i       _       = refl
  at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

  unit-other : ∀ {m} a d → (a ≡ d → ⊥) → at0 (unit {m} a) d ≡ 0
  unit-other {zero}  a       d       ne = refl
  unit-other {suc m} zero    zero    ne = ⊥-elim (ne refl)
  unit-other {suc m} zero    (suc d) ne = at-0c {m} d
  unit-other {suc m} (suc a) zero    ne = refl
  unit-other {suc m} (suc a) (suc d) ne = unit-other {m} a d (λ e → ne (cong suc e))

  *3-mono : ∀ {a b} → a ≤ b → a * 3 ≤ b * 3
  *3-mono z≤n     = z≤n
  *3-mono (s≤s l) = s≤s (s≤s (s≤s (*3-mono l)))

  ≤+ : ∀ a r → a ≤ a + r
  ≤+ zero    r = z≤n
  ≤+ (suc a) r = s≤s (≤+ a r)

  lt3 : ∀ {a b r} → a < b → r < 3 → a * 3 + r < b * 3
  lt3 {zero}  {suc b} rl′ rl = ≤-trans rl (s≤s (s≤s (s≤s z≤n)))
  lt3 {suc a} {suc b} (s≤s l) rl = s≤s (s≤s (s≤s (lt3 l rl)))

  slot-1 : ∀ {A : Set} c (x y z : A) → slot c 1 x y z ≡ y
  slot-1 true  x y z = refl
  slot-1 false x y z = refl

  slot-0 : ∀ {A : Set} c (x y : A) → slot c 0 x y x ≡ x
  slot-0 true  x y = refl
  slot-0 false x y = refl

  slot-2 : ∀ {A : Set} c (x y : A) → slot c 2 x y x ≡ x
  slot-2 true  x y = refl
  slot-2 false x y = refl

module Ends (D : GData) where
  open GData D
  private
    module K  = GB D
    module CY = Cyl K.basis
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    gs = Basis.gdeg K.basis
    g : Nat → Nat
    g k = at 0 gs k

  -- Every position below N·3 is k·3 + r.
  pos : ∀ i → i < N * 3 → Σ Nat (λ k → Σ Nat (λ r → (k < N) × ((r < 3) × (i ≡ k * 3 + r))))
  pos i iN with divmod i
  ... | (k , r , rl , e) with ≤-dec N k
  ...   | inj₁ Nk = ⊥-elim (≤-<-⊥ (≤-trans (*3-mono Nk) (≤+ (k * 3) r)) (subst (_< N * 3) e iN))
  ...   | inj₂ kN = k , r , kN , rl , e

  -- E i: i is an end generator k⊗0 or k⊗1.
  Ev : Vec Bool (N * 3)
  Ev = cylA gs (mapV (λ _ → true) gs) (mapV (λ _ → false) gs) (mapV (λ _ → true) gs)

  E : Nat → Bool
  E i = at true Ev i

  E-at : ∀ k r → k < N → r < 3 → E (k * 3 + r) ≡ slot (even (g k)) r true false true
  E-at k r kN rl =
    trans (at-cylA true gs (mapV (λ _ → true) gs) (mapV (λ _ → false) gs) (mapV (λ _ → true) gs) k r kN rl)
      (cong₂ (λ a c → slot (even (g k)) r a (at true (mapV (λ _ → false) gs) k) c)
        (at-map-lt (λ _ → true) 0 true gs k kN) (at-map-lt (λ _ → true) 0 true gs k kN)
       ∙ cong (λ b → slot (even (g k)) r true b true) (at-map-lt (λ _ → false) 0 true gs k kN))
    where
    _∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    _∙_ = trans

  -- Copies of chains at the ends are supported on E.
  SE-cyl : ∀ u w → SE E (cyl gs u 0c w)
  SE-cyl u w d Ed with ≤-dec (N * 3) d
  ... | inj₁ Nd = at-out 0 (cyl gs u 0c w) d Nd
  ... | inj₂ dN with pos d dN
  ...   | (k , r , kN , rl , refl) =
    trans (at-cylA 0 gs u 0c w k r kN rl)
      (trans (slot-F (even (g k)) r rl (trans (sym (E-at k r kN rl)) Ed) _ _ _) (at-0c {N} k))

  E-dp : ∀ i → E i ≡ true → SE E (at 0c (Basis.bplus CY.B′) i)
  E-dp i Ei with ≤-dec (N * 3) i
  ... | inj₁ Ni = subst (SE E) (sym (at-out 0c (Basis.bplus CY.B′) i Ni)) (SE-0 {N * 3} E)
  ... | inj₂ iN with pos i iN
  ...   | (k , r , kN , rl , refl) =
    subst (SE E) (sym (at-cylA 0c gs (mapV CY.c0 (Basis.bplus K.basis)) (zip3 (cyl gs) CY.OdU (Basis.bplus K.basis) CY.EvU)
                                    (mapV CY.c1 (Basis.bplus K.basis)) k r kN rl))
      (slot-T (SE E) (even (g k)) r rl (trans (sym (E-at k r kN rl)) Ei) _ _ _
        (subst (SE E) (sym (at-map-lt CY.c0 0c 0c (Basis.bplus K.basis) k kN)) (SE-cyl _ 0c))
        (subst (SE E) (sym (at-map-lt CY.c1 0c 0c (Basis.bplus K.basis) k kN)) (SE-cyl 0c _)))

  E-dm : ∀ i → E i ≡ true → SE E (at 0c (Basis.bminus CY.B′) i)
  E-dm i Ei with ≤-dec (N * 3) i
  ... | inj₁ Ni = subst (SE E) (sym (at-out 0c (Basis.bminus CY.B′) i Ni)) (SE-0 {N * 3} E)
  ... | inj₂ iN with pos i iN
  ...   | (k , r , kN , rl , refl) =
    subst (SE E) (sym (at-cylA 0c gs (mapV CY.c0 (Basis.bminus K.basis)) (zip3 (cyl gs) CY.EvU (Basis.bminus K.basis) CY.OdU)
                                    (mapV CY.c1 (Basis.bminus K.basis)) k r kN rl))
      (slot-T (SE E) (even (g k)) r rl (trans (sym (E-at k r kN rl)) Ei) _ _ _
        (subst (SE E) (sym (at-map-lt CY.c0 0c 0c (Basis.bminus K.basis) k kN)) (SE-cyl _ 0c))
        (subst (SE E) (sym (at-map-lt CY.c1 0c 0c (Basis.bminus K.basis) k kN)) (SE-cyl 0c _)))

  -- An end generator is one of the o b k.
  E-o : ∀ i → i < N * 3 → E i ≡ true → Σ Bool (λ b → Σ Nat (λ k → (k < N) × (i ≡ CollapseEnds.o D b k)))
  E-o i iN Ei with pos i iN
  ... | (k , r , kN , rl , refl) with slot-off (even (g k)) r rl (trans (sym (E-at k r kN rl)) Ei)
  ...   | (b , e) = b , k , kN , cong (k * 3 +_) (trans e (cong (λ h → off b (even h)) (K.gdeg-at k kN)))

  E-unit : ∀ a → E a ≡ true → SE E (unit {N * 3} a)
  E-unit a Ea d Ed = unit-other {N * 3} a d (λ e → tf (trans (sym Ea) (trans (cong E e) Ed)))
    where
    tf : true ≡ false → ⊥
    tf ()

  -- Degrees in the layout.
  deg-pos : ∀ k r → k < N → r < 3 → CD.A′.deg (k * 3 + r) ≡ slot (even (g k)) r (g k) (suc (g k)) (g k)
  deg-pos k r kN rl =
    trans (at-cylA 0 gs gs (mapV suc gs) gs k r kN rl)
      (cong (λ v → slot (even (g k)) r (g k) v (g k)) (at-map-lt suc 0 0 gs k kN))

  deg-mid : ∀ k → k < N → CD.A′.deg (k * 3 + 1) ≡ suc (gd k)
  deg-mid k kN = trans (deg-pos k 1 kN (s≤s (s≤s z≤n))) (trans (slot-1 (even (g k)) _ _ _) (cong suc (K.gdeg-at k kN)))

  deg-lo : ∀ k → k < N → CD.A′.deg (k * 3) ≡ gd k
  deg-lo k kN = trans (cong CD.A′.deg (sym (+-zero (k * 3))))
                  (trans (deg-pos k 0 kN (s≤s z≤n)) (trans (slot-0 (even (g k)) _ _) (K.gdeg-at k kN)))

  deg-hi : ∀ k → k < N → CD.A′.deg (k * 3 + 2) ≡ gd k
  deg-hi k kN = trans (deg-pos k 2 kN (s≤s (s≤s (s≤s z≤n)))) (trans (slot-2 (even (g k)) _ _) (K.gdeg-at k kN))

  E-lo : ∀ k → k < N → E (k * 3) ≡ true
  E-lo k kN = trans (cong E (sym (+-zero (k * 3)))) (trans (E-at k 0 kN (s≤s z≤n)) (slot-0 (even (g k)) true false))

  E-hi : ∀ k → k < N → E (k * 3 + 2) ≡ true
  E-hi k kN = trans (E-at k 2 kN (s≤s (s≤s (s≤s z≤n)))) (slot-2 (even (g k)) true false)

------------------------------------------------------------------------
-- The boundaries of F⟨k⊗i⟩ for F killing the ends.

private
  ≤-split : ∀ j n → j ≤ n → Σ Nat (λ c → n ≡ j + c)
  ≤-split zero    n       _       = n , refl
  ≤-split (suc j) (suc n) (s≤s l) with ≤-split j n l
  ... | (c , e) = c , cong suc e

  +-suc′ : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc′ zero    b = refl
  +-suc′ (suc a) b = cong suc (+-suc′ a b)

  lt-t : ∀ j k → (j <ℕ suc (j + k)) ≡ true
  lt-t zero    k = refl
  lt-t (suc j) k = lt-t j k

  ∸-+ : ∀ j k → (j + k) ∸ j ≡ k
  ∸-+ zero    k = refl
  ∸-+ (suc j) k = ∸-+ j k

  ≤+r : ∀ a c → c ≤ a + c
  ≤+r zero    c = ≤-refl c
  ≤+r (suc a) c = ≤-suc (≤+r a c)

  -- deg + 1, deg + 2, deg + 3 in the form j + d.
  sh1 : ∀ n → suc n ≡ n + 1
  sh1 n = sym (trans (+-suc′ n 0) (cong suc (+-zero n)))
  sh2 : ∀ n → suc (suc n) ≡ n + 2
  sh2 n = sym (trans (+-suc′ n 1) (cong suc (sym (sh1 n))))

module Bd (D : GData) (L : Nat) where
  open GData D
  private
    module K  = GB D
    module CY = Cyl K.basis
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    module CS = CylSplit D
    module CE = CollapseEnds D
    module EN = Ends D
    module AK = Atom K.basis
    module A′ = CD.A′
    B′ = CY.B′
    H′ = CD.Hyp′
    K′ = adc B′
    𝕄 = ADC.𝕄 K′
    module G′ = Gen B′ H′ L
    module SP = Split B′ H′ L
    module RW = Rows B′ H′ L
    module ν = ωCat (nu K′ L)
    module KL = Kill B′ H′ L EN.E EN.E-dp EN.E-dm
    0R = G′.0R

    vextT : ∀ {m} (r r′ : Tab 𝕄 m) → (∀ j → at 0R r j ≡ at 0R r′ j) → r ≡ r′
    vextT []      []        h = refl
    vextT (e ∷ r) (e′ ∷ r′) h = cong₂ _∷_ (h 0) (vextT r r′ (λ j → h (suc j)))

    at-src-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at 0R (srcT 𝕄 n x) j ≡ at 0R x j
    at-src-lt (suc n) []      j       _       = refl
    at-src-lt (suc n) (e ∷ r) zero    _       = refl
    at-src-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-lt n r j l
    at-tgt-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at 0R (tgtT 𝕄 n x) j ≡ at 0R x j
    at-tgt-lt (suc n) []      j       _       = refl
    at-tgt-lt (suc n) (e ∷ r) zero    _       = refl
    at-tgt-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-tgt-lt n r j l
    at-src-eq : ∀ {m} n (x : Tab 𝕄 m) → at 0R (srcT 𝕄 n x) n ≡ (fst (at 0R x n) , fst (at 0R x n))
    at-src-eq n       []            = refl
    at-src-eq zero    ((a , b) ∷ r) = refl
    at-src-eq (suc n) (e ∷ r)       = at-src-eq n r
    at-tgt-eq : ∀ {m} n (x : Tab 𝕄 m) → at 0R (tgtT 𝕄 n x) n ≡ (snd (at 0R x n) , snd (at 0R x n))
    at-tgt-eq n       []            = refl
    at-tgt-eq zero    ((a , b) ∷ r) = refl
    at-tgt-eq (suc n) (e ∷ r)       = at-tgt-eq n r
    at-z : ∀ {m} j → at 0R (zeros 𝕄 {m}) j ≡ 0R
    at-z {zero}  j       = refl
    at-z {suc m} zero    = refl
    at-z {suc m} (suc j) = at-z {m} j
    at-src-gt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at 0R (srcT 𝕄 n x) j ≡ 0R
    at-src-gt n       []            j       l       = refl
    at-src-gt {suc m} zero ((a , b) ∷ r) (suc j) l = at-z {m} j
    at-src-gt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-gt n r j l
    at-tgt-gt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at 0R (tgtT 𝕄 n x) j ≡ 0R
    at-tgt-gt n       []            j       l       = refl
    at-tgt-gt {suc m} zero ((a , b) ∷ r) (suc j) l = at-z {m} j
    at-tgt-gt (suc n) (e ∷ r) (suc j) (s≤s l) = at-tgt-gt n r j l

    ent-eq : ∀ i j d → A′.deg i ≡ j + d → A′.ent i j ≡ A′.entK i d
    ent-eq i j d e =
      trans (cong (λ n → if j <ℕ suc n then A′.entK i (n ∸ j) else (0c , 0c)) e) go
      where
      go : (if j <ℕ suc (j + d) then A′.entK i ((j + d) ∸ j) else (0c , 0c)) ≡ A′.entK i d
      go rewrite lt-t j d | ∸-+ j d = refl

  -- Rows above s of the form W s v are supported on E when v is.
  SER-W : ∀ s v → SE EN.E v → ∀ j → s < j → KL.SER (G′.W s v j)
  SER-W s v h j l with tri j (suc s)
  ... | tri< l′   = ⊥-elim (≤-<-⊥ l l′)
  ... | tri≡ refl = subst KL.SER (sym (G′.W-top s v)) (h , h)
  ... | tri> l′   = subst KL.SER (sym (G′.W-above s v j l′)) (SE-0 {N * 3} EN.E , SE-0 {N * 3} EN.E)

  -- Positions and degrees for k of degree g′ + 1.
  module At (k : Nat) (kN : k < N) (p : 1 ≤ gd k) (g′ : Nat) (e : gd k ≡ suc g′) (kL : suc (gd k) ≤ L) where
    ki ski tki : Nat
    ki  = k * 3 + 1
    ski = s k * 3 + 1
    tki = t k * 3 + 1
    skN = sN k kN p
    tkN = tN k kN p
    kiN : ki < N * 3
    kiN = lt3 kN (s≤s (s≤s z≤n))
    skiN : ski < N * 3
    skiN = lt3 skN (s≤s (s≤s z≤n))
    tkiN : tki < N * 3
    tkiN = lt3 tkN (s≤s (s≤s z≤n))
    k3N : k * 3 < N * 3
    k3N = ≤-trans (s≤s (≤+ (k * 3) 1)) kiN
    k32N : k * 3 + 2 < N * 3
    k32N = lt3 kN (s≤s (s≤s (s≤s z≤n)))
    dki : A′.deg ki ≡ suc (suc g′)
    dki = trans (EN.deg-mid k kN) (cong suc e)
    dski : A′.deg ski ≡ suc g′
    dski = trans (EN.deg-mid (s k) skN) (cong suc (trans (ds k kN p) (cong (_∸ 1) e)))
    dtki : A′.deg tki ≡ suc g′
    dtki = trans (EN.deg-mid (t k) tkN) (cong suc (trans (dt k kN p) (cong (_∸ 1) e)))
    dk3 : A′.deg (k * 3) ≡ suc g′
    dk3 = trans (EN.deg-lo k kN) e
    dk32 : A′.deg (k * 3 + 2) ≡ suc g′
    dk32 = trans (EN.deg-hi k kN) e
    degsk : AK.deg (s k) ≡ g′
    degsk = trans (K.gdeg-at (s k) skN) (trans (ds k kN p) (cong (_∸ 1) e))
    degtk : AK.deg (t k) ≡ g′
    degtk = trans (K.gdeg-at (t k) tkN) (trans (dt k kN p) (cong (_∸ 1) e))
    kL′ : suc (suc g′) ≤ L
    kL′ = subst (λ m → suc m ≤ L) e kL
    gL : suc g′ ≤ L
    gL = ≤-trans (≤-suc (≤-refl _)) kL′
    kiL : A′.deg ki ≤ L
    kiL = subst (_≤ L) (sym dki) kL′
    skiL : A′.deg ski ≤ L
    skiL = subst (_≤ L) (sym dski) gL
    tkiL : A′.deg tki ≤ L
    tkiL = subst (_≤ L) (sym dtki) gL
    jL : ∀ j → j ≤ suc g′ → j ≤ L
    jL j l = ≤-trans l gL

    A As At : Cell K′ L
    A  = G′.atom ki kiN kiL
    As = G′.atom ski skiN skiL
    At = G′.atom tki tkiN tkiL

    row : ∀ i iN iL j → j ≤ L → at 0R (A′.atomT L i) j ≡ A′.ent i j
    row i iN iL j l = RW.rows-atom i iN iL j l

    -- Rows of ⟨k⊗i⟩, ⟨sk⊗i⟩, ⟨tk⊗i⟩ at degree j ≤ g′ + 1 by depth.
    ent-k : ∀ j c → suc g′ ≡ j + c → A′.ent ki j ≡ A′.entK ki (suc c)
    ent-k j c h = ent-eq ki j (suc c) (trans dki (trans (cong suc h) (sym (+-suc′ j c))))
    ent-s : ∀ j c → suc g′ ≡ j + c → A′.ent ski j ≡ A′.entK ski c
    ent-s j c h = ent-eq ski j c (trans dski h)
    ent-t : ∀ j c → suc g′ ≡ j + c → A′.ent tki j ≡ A′.entK tki c
    ent-t j c h = ent-eq tki j c (trans dtki h)

    SRC : srcT 𝕄 g′ (fst A) ≡ srcT 𝕄 g′ (fst As)
    SRC = vextT _ _ pt
      where
      pt : ∀ j → at 0R (srcT 𝕄 g′ (fst A)) j ≡ at 0R (srcT 𝕄 g′ (fst As)) j
      pt j with tri j g′
      ... | tri< jl with ≤-split (suc j) g′ jl
      ...   | (c , eg) =
        trans (at-src-lt g′ (fst A) j jl)
          (trans (row ki kiN kiL j jL′)
            (trans (ent-k j (suc (suc c)) h)
              (trans (cong₂ _,_ (CS.fst-s k kN p (suc (suc c)) (s≤s z≤n) bd) (CS.snd-s k kN p2 (suc (suc c)) (s≤s (s≤s z≤n)) bd))
                (trans (sym (ent-s j (suc (suc c)) h))
                  (trans (sym (row ski skiN skiL j jL′)) (sym (at-src-lt g′ (fst As) j jl)))))))
        where
        h : suc g′ ≡ j + suc (suc c)
        h = trans (cong suc eg) (sym (trans (+-suc′ j (suc c)) (cong suc (+-suc′ j c))))
        jL′ = jL j (≤-trans (≤-suc (≤-refl j)) (≤-trans jl (≤-suc (≤-refl g′))))
        bd : suc (suc c) ≤ suc (AK.deg (s k))
        bd = subst (λ m → suc (suc c) ≤ suc m) (sym (trans degsk eg)) (s≤s (s≤s (≤+r j c)))
        p2 : 2 ≤ gd k
        p2 = subst (2 ≤_) (sym (trans e (cong suc eg))) (s≤s (s≤s z≤n))
      pt j | tri≡ refl =
        trans (at-src-eq g′ (fst A))
          (trans (cong (λ r → (fst r , fst r)) (trans (row ki kiN kiL g′ (jL g′ (≤-suc (≤-refl g′)))) (ent-k g′ 1 (sh1 g′))))
            (trans (cong (λ v → (v , v)) (CS.fst-s k kN p 1 (s≤s z≤n) (s≤s z≤n)))
              (sym (trans (at-src-eq g′ (fst As))
                (cong (λ r → (fst r , fst r)) (trans (row ski skiN skiL g′ (jL g′ (≤-suc (≤-refl g′)))) (ent-s g′ 1 (sh1 g′))))))))
      pt j | tri> l = trans (at-src-gt g′ (fst A) j l) (sym (at-src-gt g′ (fst As) j l))

    TGT : tgtT 𝕄 g′ (fst A) ≡ tgtT 𝕄 g′ (fst At)
    TGT = vextT _ _ pt
      where
      pt : ∀ j → at 0R (tgtT 𝕄 g′ (fst A)) j ≡ at 0R (tgtT 𝕄 g′ (fst At)) j
      pt j with tri j g′
      ... | tri< jl with ≤-split (suc j) g′ jl
      ...   | (c , eg) =
        trans (at-tgt-lt g′ (fst A) j jl)
          (trans (row ki kiN kiL j jL′)
            (trans (ent-k j (suc (suc c)) h)
              (trans (cong₂ _,_ (CS.fst-t k kN p2 (suc (suc c)) (s≤s (s≤s z≤n)) bd) (CS.snd-t k kN p (suc (suc c)) (s≤s z≤n) bd))
                (trans (sym (ent-t j (suc (suc c)) h))
                  (trans (sym (row tki tkiN tkiL j jL′)) (sym (at-tgt-lt g′ (fst At) j jl)))))))
        where
        h : suc g′ ≡ j + suc (suc c)
        h = trans (cong suc eg) (sym (trans (+-suc′ j (suc c)) (cong suc (+-suc′ j c))))
        jL′ = jL j (≤-trans (≤-suc (≤-refl j)) (≤-trans jl (≤-suc (≤-refl g′))))
        bd : suc (suc c) ≤ suc (AK.deg (t k))
        bd = subst (λ m → suc (suc c) ≤ suc m) (sym (trans degtk eg)) (s≤s (s≤s (≤+r j c)))
        p2 : 2 ≤ gd k
        p2 = subst (2 ≤_) (sym (trans e (cong suc eg))) (s≤s (s≤s z≤n))
      pt j | tri≡ refl =
        trans (at-tgt-eq g′ (fst A))
          (trans (cong (λ r → (snd r , snd r)) (trans (row ki kiN kiL g′ (jL g′ (≤-suc (≤-refl g′)))) (ent-k g′ 1 (sh1 g′))))
            (trans (cong (λ v → (v , v)) (CS.snd-t k kN p 1 (s≤s z≤n) (s≤s z≤n)))
              (sym (trans (at-tgt-eq g′ (fst At))
                (cong (λ r → (snd r , snd r)) (trans (row tki tkiN tkiL g′ (jL g′ (≤-suc (≤-refl g′)))) (ent-t g′ 1 (sh1 g′))))))))
      pt j | tri> l = trans (at-tgt-gt g′ (fst A) j l) (sym (at-tgt-gt g′ (fst At) j l))

    -- The top row of the boundaries of ⟨k⊗i⟩.
    top : at 0R (fst A) (suc g′) ≡ A′.entK ki 1
    top = trans (row ki kiN kiL (suc g′) gL) (ent-eq ki (suc g′) 1 (trans dki (sh1 (suc g′))))

    src-rows : ∀ j → g′ < j → at 0R (srcT 𝕄 (suc g′) (fst A)) j ≡ G′.W g′ (unit ski +c unit (k * 3)) j
    src-rows j l with tri j (suc g′)
    ... | tri< l′   = ⊥-elim (≤-<-⊥ l l′)
    ... | tri≡ refl =
      trans (at-src-eq (suc g′) (fst A))
        (trans (cong (λ r → (fst r , fst r)) (trans top (CS.row-top k kN p))) (sym (G′.W-top g′ _)))
    ... | tri> l′   = trans (at-src-gt (suc g′) (fst A) j l′) (sym (G′.W-above g′ _ j l′))

    tgt-rows : ∀ j → g′ < j → at 0R (tgtT 𝕄 (suc g′) (fst A)) j ≡ G′.W g′ (unit (k * 3 + 2) +c unit tki) j
    tgt-rows j l with tri j (suc g′)
    ... | tri< l′   = ⊥-elim (≤-<-⊥ l l′)
    ... | tri≡ refl =
      trans (at-tgt-eq (suc g′) (fst A))
        (trans (cong (λ r → (snd r , snd r)) (trans top (CS.row-top k kN p))) (sym (G′.W-top g′ _)))
    ... | tri> l′   = trans (at-tgt-gt (suc g′) (fst A) j l′) (sym (G′.W-above g′ _ j l′))

  -- A functor that sends each end atom ⟨k⊗0⟩ to P true and ⟨k⊗1⟩ to P false, both points.
  module _ {𝒟 : ωCat} (Φ : G′.Functor 𝒟) (P : Bool → ωCat.C 𝒟)
           (P0 : ∀ b → Basics.Dim≤ 𝒟 0 (P b))
           (ends : ∀ b k (kN : k < N) aN aL → G′.Functor.F Φ (G′.atom (CE.o b k) aN aL) ≡ P b) where
    private
      module 𝒟 = ωCat 𝒟
      open Basics 𝒟 using (Dim≤; comp-cong; tgt-of-dim)
      open G′.Functor Φ

    F-at : ∀ {a a′} → a ≡ a′ → ∀ aN aL aN′ aL′ → F (G′.atom a aN aL) ≡ F (G′.atom a′ aN′ aL′)
    F-at refl aN aL aN′ aL′ = cong F (≡-cell K′ L refl)

    killed : ∀ a aN aL → EN.E a ≡ true → Dim≤ 0 (F (G′.atom a aN aL))
    killed a aN aL Ea = go (EN.E-o a aN Ea)
      where
      go : Σ Bool (λ b → Σ Nat (λ k → (k < N) × (a ≡ CE.o b k))) → Dim≤ 0 (F (G′.atom a aN aL))
      go (b , k , kN , e) =
        subst (Dim≤ 0) (sym (trans (F-at e aN aL (CE.o-N b k kN) oL) (ends b k kN (CE.o-N b k kN) oL))) (P0 b)
        where
        oL = subst (λ i → A′.deg i ≤ L) e aL

    flat : ∀ r (z : Cell K′ L) v → SE EN.E v → (∀ j → r < j → at 0R (fst z) j ≡ G′.W r v j) → Dim≤ r (F z)
    flat r z v hv zr = KL.kill Φ killed r z (λ j l → subst KL.SER (sym (zr j l)) (SER-W r v hv j l))

    -- src_m F⟨k⊗i⟩ = F⟨sk⊗i⟩ for deg k = m = g′ + 1.
    bd-src′ : ∀ k (kN : k < N) (p : 1 ≤ gd k) g′ (e : gd k ≡ suc g′) (kL : suc (gd k) ≤ L) →
              𝒟.src (suc g′) (F (At.A k kN p g′ e kL)) ≡ F (At.As k kN p g′ e kL)
    bd-src′ k kN p g′ e kL =
      trans (sym (F-src (suc g′) A))
        (trans (cong F (sym ce))
          (trans (F-comp g′ As Z pm q)
            (trans (comp-cong g′ q q′ refl fz) (𝒟.unit-r g′ (F As) q′))))
      where
      open At k kN p g′ e kL
      x = ν.src (suc g′) A
      xs : srcT 𝕄 g′ (fst x) ≡ srcT 𝕄 g′ (A′.atomT L ski)
      xs = trans (cong fst (ν.src-src-< A (≤-refl (suc g′)))) SRC
      S = SP.split-src g′ ski (k * 3) skiN k3N (lt3 (s-lt k kN p) (s≤s (s≤s z≤n))) dski dk3 gL
            (fst x) (snd x) src-rows xs
      Z : Cell K′ L
      Z = fst (fst S) , fst (snd (fst S))
      pm : ν.tgt g′ As ≡ ν.src g′ Z
      pm = ≡-cell K′ L (fst (snd S))
      ce : ν.comp g′ As Z pm ≡ x
      ce = ≡-cell K′ L (snd (snd S))
      q : 𝒟.tgt g′ (F As) ≡ 𝒟.src g′ (F Z)
      q = trans (sym (F-tgt g′ As)) (trans (cong F pm) (F-src g′ Z))
      dz : Dim≤ g′ (F Z)
      dz = flat g′ Z (unit (k * 3)) (EN.E-unit (k * 3) (EN.E-lo k kN)) (snd (snd (fst S)))
      fz : F Z ≡ 𝒟.tgt g′ (F As)
      fz = trans (sym dz) (sym q)
      q′ : 𝒟.tgt g′ (F As) ≡ 𝒟.src g′ (𝒟.tgt g′ (F As))
      q′ = sym (𝒟.src-tgt-≥ (F As) (≤-refl g′))

    -- tgt_m F⟨k⊗i⟩ = F⟨tk⊗i⟩.
    bd-tgt′ : ∀ k (kN : k < N) (p : 1 ≤ gd k) g′ (e : gd k ≡ suc g′) (kL : suc (gd k) ≤ L) →
              𝒟.tgt (suc g′) (F (At.A k kN p g′ e kL)) ≡ F (At.At k kN p g′ e kL)
    bd-tgt′ k kN p g′ e kL =
      trans (sym (F-tgt (suc g′) A))
        (trans (cong F (sym ce))
          (trans (F-comp g′ Z At pm q)
            (trans (comp-cong g′ q q′ fz refl) (𝒟.unit-l g′ (F At) q′))))
      where
      open At k kN p g′ e kL
      x = ν.tgt (suc g′) A
      xt : tgtT 𝕄 g′ (fst x) ≡ tgtT 𝕄 g′ (A′.atomT L tki)
      xt = trans (cong fst (ν.tgt-tgt-< A (≤-refl (suc g′)))) TGT
      S = SP.split-tgt g′ (k * 3 + 2) tki k32N tkiN
            (≤-trans (lt3 (t-gt k kN p) (s≤s (s≤s (s≤s z≤n)))) (≤+ (t k * 3) 1)) dk32 dtki gL
            (fst x) (snd x) tgt-rows xt
      Z : Cell K′ L
      Z = fst (fst S) , fst (snd (fst S))
      pm : ν.tgt g′ Z ≡ ν.src g′ At
      pm = ≡-cell K′ L (fst (snd S))
      ce : ν.comp g′ Z At pm ≡ x
      ce = ≡-cell K′ L (snd (snd S))
      q : 𝒟.tgt g′ (F Z) ≡ 𝒟.src g′ (F At)
      q = trans (sym (F-tgt g′ Z)) (trans (cong F pm) (F-src g′ At))
      dz : Dim≤ g′ (F Z)
      dz = flat g′ Z (unit (k * 3 + 2)) (EN.E-unit (k * 3 + 2) (EN.E-hi k kN)) (snd (snd (fst S)))
      fz : F Z ≡ 𝒟.src g′ (F At)
      fz = trans (sym (tgt-of-dim dz)) q
      q′ : 𝒟.tgt g′ (𝒟.src g′ (F At)) ≡ 𝒟.src g′ (F At)
      q′ = 𝒟.tgt-src-≥ (F At) (≤-refl g′)

------------------------------------------------------------------------
-- The correspondence.

-- Composition of strict functors.
_∘F_ : ∀ {𝒜 ℬ 𝒞 : ωCat} → Functor ℬ 𝒞 → Functor 𝒜 ℬ → Functor 𝒜 𝒞
_∘F_ {𝒜} {ℬ} {𝒞} G F = record
  { F      = λ x → G.F (F.F x)
  ; F-src  = λ n x → trans (cong G.F (F.F-src n x)) (G.F-src n (F.F x))
  ; F-tgt  = λ n x → trans (cong G.F (F.F-tgt n x)) (G.F-tgt n (F.F x))
  ; F-comp = λ n x y p q →
      let q′ = trans (sym (F.F-tgt n x)) (trans (cong F.F p) (F.F-src n y)) in
      trans (cong G.F (F.F-comp n x y p q′)) (G.F-comp n (F.F x) (F.F y) q′ q)
  }
  where
  module G = Functor G
  module F = Functor F

private
  slot-mid : ∀ c r → r < 3 → slot c r true false true ≡ false → r ≡ 1
  slot-mid true  zero                _ ()
  slot-mid true  (suc zero)          _ _ = refl
  slot-mid true  (suc (suc zero))    _ ()
  slot-mid false zero                _ ()
  slot-mid false (suc zero)          _ _ = refl
  slot-mid false (suc (suc zero))    _ ()
  slot-mid c     (suc (suc (suc r))) (s≤s (s≤s (s≤s ())))

  ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym z≤n     z≤n     = refl
  ≤-antisym (s≤s l) (s≤s m) = cong suc (≤-antisym l m)

module Corr (D : GData) (L : Nat) (𝒟 : ωCat) where
  open GData D
  private
    module K  = GB D
    module S  = GB (Σg D)
    module CY = Cyl K.basis
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    module CO = Collapse D
    module CA = CollapseAtoms D
    module CE = CollapseEnds D
    module CS = CylSplit D
    module EN = Ends D
    module BD = Bd D L
    module GK = GA D
    module A′ = CD.A′
    module AK = Atom K.basis
    module AS = Atom S.basis
    module 𝒟 = ωCat 𝒟
    B′ = CY.B′
    H′ = CD.Hyp′
    K′ = adc B′
    KS = adc S.basis
    𝕄 = ADC.𝕄 K′
    module G′ = Gen B′ H′ L
    module GS = Gen S.basis S.hyp L
    module RW = Rows B′ H′ L
    module RS = Rows S.basis S.hyp L
    module ν = ωCat (nu K′ L)
    module νS = ωCat (nu KS L)
    open Basics 𝒟 using (Dim≤; dim-up)

  -- ν(λD ⊗ λD¹), ν(Σ λD) and ν(q) between them.
  Cyl𝒞 Sus𝒞 : ωCat
  Cyl𝒞 = nu K′ L
  Sus𝒞 = nu KS L

  νq : Functor Cyl𝒞 Sus𝒞
  νq = CO.νq L

  -- F sends every ⟨k⊗0⟩ to the point P true and every ⟨k⊗1⟩ to P false.
  record EndsAt (Φ : Functor Cyl𝒞 𝒟) (P : Bool → ωCat.C 𝒟) : Set where
    field
      P0   : ∀ b → Dim≤ 0 (P b)
      ends : ∀ b k (kN : k < N) aN aL → Functor.F Φ (G′.atom (CE.o b k) aN aL) ≡ P b

  private
    toGen : Functor Cyl𝒞 𝒟 → G′.Functor 𝒟
    toGen Φ = record { F = Functor.F Φ ; F-src = Functor.F-src Φ ; F-tgt = Functor.F-tgt Φ ; F-comp = Functor.F-comp Φ }

    gΣk = CO.Aux.gΣk

    kiN : ∀ k → k < N → k * 3 + 1 < N * 3
    kiN k kN = lt3 kN (s≤s (s≤s z≤n))

    -- The points of Σ D have degree 0; Σk has degree deg k + 1.
    deg⊥ : AS.deg 0 ≡ 0
    deg⊥ = CO.Aux.gΣ0
    deg⊤ : ∀ k → N ≤ k → suc k < suc (suc N) → AS.deg (suc k) ≡ 0
    deg⊤ k Nk (s≤s l) = trans (cong (λ h → AS.deg (suc h)) (≤-antisym (≤-pred′ l) Nk)) CO.Aux.gΣ⊤
      where
      ≤-pred′ : ∀ {a b} → suc a ≤ suc b → a ≤ b
      ≤-pred′ (s≤s l) = l

    -- The generator 0 of D is a point.
    gd0 : 0 < N → gd 0 ≡ 0
    gd0 l with gd 0 in e
    ... | zero  = refl
    ... | suc _ = ⊥-elim (no (s-lt 0 l (subst (1 ≤_) (sym e) (s≤s z≤n))))
      where
      no : ∀ {a} → a < 0 → ⊥
      no ()

    mid-deg : ∀ k → k < N → A′.deg (k * 3 + 1) ≡ AS.deg (suc k)
    mid-deg k kN = trans (EN.deg-mid k kN) (sym (gΣk k kN))

    -- Atoms of degree 0 and 1.
    0R = G′.0R

    vextT : ∀ {m} (r r′ : Tab 𝕄 m) → (∀ j → at 0R r j ≡ at 0R r′ j) → r ≡ r′
    vextT []      []        h = refl
    vextT (e ∷ r) (e′ ∷ r′) h = cong₂ _∷_ (h 0) (vextT r r′ (λ j → h (suc j)))

    at-z : ∀ {m} j → at 0R (zeros 𝕄 {m}) j ≡ 0R
    at-z {zero}  j       = refl
    at-z {suc m} zero    = refl
    at-z {suc m} (suc j) = at-z {m} j
    at-src-gt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at 0R (srcT 𝕄 n x) j ≡ 0R
    at-src-gt n       []            j       l       = refl
    at-src-gt {suc m} zero ((a , b) ∷ r) (suc j) l = at-z {m} j
    at-src-gt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-gt n r j l
    at-tgt-gt : ∀ {m} n (x : Tab 𝕄 m) j → n < j → at 0R (tgtT 𝕄 n x) j ≡ 0R
    at-tgt-gt n       []            j       l       = refl
    at-tgt-gt {suc m} zero ((a , b) ∷ r) (suc j) l = at-z {m} j
    at-tgt-gt (suc n) (e ∷ r) (suc j) (s≤s l) = at-tgt-gt n r j l

    at-out′ : ∀ {m} (vs : Tab 𝕄 m) i → m ≤ i → at 0R vs i ≡ 0R
    at-out′ []       i       _       = refl
    at-out′ (v ∷ vs) (suc i) (s≤s q) = at-out′ vs i q

  module _ (Φ : Functor Cyl𝒞 𝒟) where
    open Functor Φ using (F; F-src)

    F-at : ∀ {a a′} → a ≡ a′ → ∀ aN aL aN′ aL′ → F (G′.atom a aN aL) ≡ F (G′.atom a′ aN′ aL′)
    F-at refl aN aL aN′ aL′ = cong F (≡-cell K′ L refl)

    dim-F : ∀ a aN aL → Dim≤ (A′.deg a) (F (G′.atom a aN aL))
    dim-F a aN aL = trans (sym (F-src (A′.deg a) (G′.atom a aN aL))) (cong F (RW.dim-atom a aN aL))

  -- For deg k = 0, the boundaries of ⟨k⊗i⟩ are ⟨k⊗0⟩ and ⟨k⊗1⟩.
  module Low (k : Nat) (kN : k < N) (e : gd k ≡ 0) (aL : A′.deg (k * 3 + 1) ≤ L) where
    oL : ∀ b → A′.deg (CE.o b k) ≤ L
    oL b = subst (_≤ L) (sym (trans (CE.deg-o b k kN) e)) z≤n
    private
      ki = k * 3 + 1
      A = G′.atom ki (kiN k kN) aL
      dA : A′.deg ki ≡ 1
      dA = trans (EN.deg-mid k kN) (cong suc e)
      dk : AK.deg k ≡ 0
      dk = trans (K.gdeg-at k kN) e
      bot : AK.entK k 1 ≡ (0c , 0c)
      bot = trans (cong (λ d → AK.entK k (suc d)) (sym e)) (GK.entK-bot k kN)
      top : A′.entK ki 1 ≡ (CD.F true (unit k) 0c , CD.G true (unit k) 0c)
      top = trans (CS.form k kN 1 (subst (λ d → 1 ≤ suc d) (sym dk) (s≤s z≤n)))
                  (trans (cong (λ d → (CD.F (P̂ d 1) (unit k) (fst (AK.entK k 1)) , CD.G (P̂ d 1) (unit k) (snd (AK.entK k 1)))) dk)
                         (cong (λ r → (CD.F true (unit k) (fst r) , CD.G true (unit k) (snd r))) bot))
      row0 : at 0R (fst A) 0 ≡ (unit (CE.o true k) , unit (CE.o false k))
      row0 = trans (RW.rows-atom ki (kiN k kN) aL 0 z≤n)
               (trans (cong (λ n → if 0 <ℕ suc n then A′.entK ki (n ∸ 0) else (0c , 0c)) dA)
                 (trans top (cong₂ _,_ (sym (CE.u-o true k kN)) (sym (CE.u-o false k kN)))))
      pt-rows : ∀ b j → at 0R (fst (G′.atom (CE.o b k) (CE.o-N b k kN) (oL b))) j ≡
                         (if j ==ℕ 0 then (unit (CE.o b k) , unit (CE.o b k)) else 0R)
      pt-rows b zero    = trans (RW.rows-atom (CE.o b k) (CE.o-N b k kN) (oL b) 0 z≤n)
                            (cong (λ n → if 0 <ℕ suc n then A′.entK (CE.o b k) (n ∸ 0) else (0c , 0c)) (trans (CE.deg-o b k kN) e))
      pt-rows b (suc j) with ≤-dec (suc j) L
      ... | inj₁ jL = trans (RW.rows-atom (CE.o b k) (CE.o-N b k kN) (oL b) (suc j) jL)
                        (G′.ent-zero (CE.o b k) (suc j) (subst (_< suc j) (sym (trans (CE.deg-o b k kN) e)) (s≤s z≤n)))
      ... | inj₂ Lj = at-out′ (fst (G′.atom (CE.o b k) (CE.o-N b k kN) (oL b))) (suc j) Lj

    src0 : ν.src 0 A ≡ G′.atom (CE.o true k) (CE.o-N true k kN) (oL true)
    src0 = ≡-cell K′ L (vextT _ _ pt)
      where
      pt : ∀ j → at 0R (srcT 𝕄 0 (fst A)) j ≡ at 0R (fst (G′.atom (CE.o true k) (CE.o-N true k kN) (oL true))) j
      pt zero    = trans (cong (λ r → (fst r , fst r)) row0) (sym (pt-rows true 0))
      pt (suc j) = trans (at-src-gt 0 (fst A) (suc j) (s≤s z≤n)) (sym (pt-rows true (suc j)))

    tgt0 : ν.tgt 0 A ≡ G′.atom (CE.o false k) (CE.o-N false k kN) (oL false)
    tgt0 = ≡-cell K′ L (vextT _ _ pt)
      where
      pt : ∀ j → at 0R (tgtT 𝕄 0 (fst A)) j ≡ at 0R (fst (G′.atom (CE.o false k) (CE.o-N false k kN) (oL false))) j
      pt zero    = trans (cong (λ r → (snd r , snd r)) row0) (sym (pt-rows false 0))
      pt (suc j) = trans (at-tgt-gt 0 (fst A) (suc j) (s≤s z≤n)) (sym (pt-rows false (suc j)))

  ----------------------------------------------------------------------
  -- Existence: F factors through ν(q).

  private
    ibN : ∀ b → CE.ib b < suc (suc N)
    ibN true  = s≤s z≤n
    ibN false = ≤-refl _
    deg-ib : ∀ b → AS.deg (CE.ib b) ≡ 0
    deg-ib true  = deg⊥
    deg-ib false = CO.Aux.gΣ⊤
    ibL : ∀ b → AS.deg (CE.ib b) ≤ L
    ibL b = subst (_≤ L) (sym (deg-ib b)) z≤n
    no1 : 1 ≤ 0 → ⊥
    no1 ()

  module FO = FreeOn (Σg D) L

  module Exists (Φ : Functor Cyl𝒞 𝒟) (P : Bool → ωCat.C 𝒟) (h : EndsAt Φ P) where
    private
      open Functor Φ
      open EndsAt h
      kiL : ∀ k → k < N → AS.deg (suc k) ≤ L → A′.deg (k * 3 + 1) ≤ L
      kiL k kN l = subst (_≤ L) (sym (mid-deg k kN)) l

    -- The value at Σk or ⊤, by whether k < N (no `with`, so the goals stay small).
    κm : ∀ k → AS.deg (suc k) ≤ L → (N ≤ k) ⊎ (k < N) → 𝒟.C
    κm k dL (inj₁ _)  = P false
    κm k dL (inj₂ kN) = F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL))

    κ : FO.G → 𝒟.C
    κ (zero  , _ , _)  = P true
    κ (suc k , l , dL) = κm k dL (≤-dec N k)

    κm-irr : ∀ k dL dL′ d → κm k dL d ≡ κm k dL′ d
    κm-irr k dL dL′ (inj₁ _)  = refl
    κm-irr k dL dL′ (inj₂ kN) = F-at Φ refl (kiN k kN) (kiL k kN dL) (kiN k kN) (kiL k kN dL′)

    κ-irr : ∀ i l dL l′ dL′ → κ (i , l , dL) ≡ κ (i , l′ , dL′)
    κ-irr zero    l dL l′ dL′ = refl
    κ-irr (suc k) l dL l′ dL′ = κm-irr k dL dL′ (≤-dec N k)

    κm-mid : ∀ k dL d → k < N → ∀ aN aL → κm k dL d ≡ F (G′.atom (k * 3 + 1) aN aL)
    κm-mid k dL (inj₁ Nk)  kN aN aL = ⊥-elim (≤-<-⊥ Nk kN)
    κm-mid k dL (inj₂ kN′) kN aN aL = F-at Φ refl (kiN k kN′) (kiL k kN′ dL) aN aL

    κ-mid : ∀ k (kN : k < N) l dL aN aL → κ (suc k , l , dL) ≡ F (G′.atom (k * 3 + 1) aN aL)
    κ-mid k kN l dL aN aL = κm-mid k dL (≤-dec N k) kN aN aL

    κm-top : ∀ dL d → κm N dL d ≡ P false
    κm-top dL (inj₁ _)  = refl
    κm-top dL (inj₂ NN) = ⊥-elim (≤-<-⊥ (≤-refl N) NN)

    κ-top : ∀ l dL → κ (suc N , l , dL) ≡ P false
    κ-top l dL = κm-top dL (≤-dec N N)

    κ-ib : ∀ b l dL → κ (CE.ib b , l , dL) ≡ P b
    κ-ib true  l dL = refl
    κ-ib false l dL = κ-top l dL

    dimκm : ∀ k (l : suc k < suc (suc N)) dL d → 𝒟.src (AS.deg (suc k)) (κm k dL d) ≡ κm k dL d
    dimκm k l dL (inj₁ _)  = dim-up z≤n (P0 false)
    dimκm k l dL (inj₂ kN) =
      subst (λ d → Dim≤ d (F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL)))) (mid-deg k kN) (dim-F Φ (k * 3 + 1) (kiN k kN) (kiL k kN dL))

    dimκ : ∀ g → 𝒟.src (FO.degG g) (κ g) ≡ κ g
    dimκ (zero  , _ , _)  = dim-up z≤n (P0 true)
    dimκ (suc k , l , dL) = dimκm k l dL (≤-dec N k)

    private
      Φg = toGen Φ

      -- The boundary conditions at Σk, by the degree of k.
      bs : ∀ k (kN : k < N) (l : suc k < suc (suc N)) dL → ∀ g (e : gd k ≡ g) (l′ : _ < suc (suc N)) dL′ →
           𝒟.src g (F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL))) ≡
           κ ((if g ==ℕ 0 then 0 else suc (s k)) , l′ , dL′)
      bs k kN l dL zero e l′ dL′ =
        trans (sym (F-src 0 _))
          (trans (cong F (Low.src0 k kN e (kiL k kN dL)))
            (ends true k kN (CE.o-N true k kN) (Low.oL k kN e (kiL k kN dL) true)))
      bs k kN l dL (suc g′) e l′ dL′ =
        trans (cong (𝒟.src (suc g′)) (F-at Φ refl (kiN k kN) (kiL k kN dL) AT.kiN AT.kiL))
          (trans (BD.bd-src′ Φg P P0 ends k kN p g′ e kL)
            (sym (κ-mid (s k) skN l′ dL′ AT.skiN AT.skiL)))
        where
        p : 1 ≤ gd k
        p = subst (1 ≤_) (sym e) (s≤s z≤n)
        kL : suc (gd k) ≤ L
        kL = subst (_≤ L) (gΣk k kN) dL
        skN = sN k kN p
        module AT = BD.At k kN p g′ e kL

      bt : ∀ k (kN : k < N) (l : suc k < suc (suc N)) dL → ∀ g (e : gd k ≡ g) (l′ : _ < suc (suc N)) dL′ →
           𝒟.tgt g (F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL))) ≡
           κ ((if g ==ℕ 0 then suc N else suc (t k)) , l′ , dL′)
      bt k kN l dL zero e l′ dL′ =
        trans (sym (F-tgt 0 _))
          (trans (cong F (Low.tgt0 k kN e (kiL k kN dL)))
            (trans (ends false k kN (CE.o-N false k kN) (Low.oL k kN e (kiL k kN dL) false)) (sym (κ-top l′ dL′))))
      bt k kN l dL (suc g′) e l′ dL′ =
        trans (cong (𝒟.tgt (suc g′)) (F-at Φ refl (kiN k kN) (kiL k kN dL) AT.kiN AT.kiL))
          (trans (BD.bd-tgt′ Φg P P0 ends k kN p g′ e kL)
            (sym (κ-mid (t k) tkN l′ dL′ AT.tkiN AT.tkiL)))
        where
        p : 1 ≤ gd k
        p = subst (1 ≤_) (sym e) (s≤s z≤n)
        kL : suc (gd k) ≤ L
        kL = subst (_≤ L) (gΣk k kN) dL
        tkN = tN k kN p
        module AT = BD.At k kN p g′ e kL

    κsm : ∀ k (l : suc k < suc (suc N)) dL (dg : 1 ≤ AS.deg (suc k)) d → ∀ l′ dL′ →
          𝒟.src (AS.deg (suc k) ∸ 1) (κm k dL d) ≡ κ ((if gd k ==ℕ 0 then 0 else suc (s k)) , l′ , dL′)
    κsm k l dL dg (inj₁ Nk) l′ dL′ = ⊥-elim (no1 (subst (1 ≤_) (deg⊤ k Nk l) dg))
    κsm k l dL dg (inj₂ kN) l′ dL′ =
      trans (cong (λ d → 𝒟.src d (F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL)))) (cong (_∸ 1) (gΣk k kN)))
        (bs k kN l dL (gd k) refl l′ dL′)

    κs : ∀ g (dg : 1 ≤ FO.degG g) → 𝒟.src (FO.degG g ∸ 1) (κ g) ≡ κ (FO.sG g dg)
    κs (zero  , _ , _)  dg = ⊥-elim (no1 (subst (1 ≤_) deg⊥ dg))
    κs (suc k , l , dL) dg = κsm k l dL dg (≤-dec N k) (fst (snd (FO.sG (suc k , l , dL) dg))) (snd (snd (FO.sG (suc k , l , dL) dg)))

    κtm : ∀ k (l : suc k < suc (suc N)) dL (dg : 1 ≤ AS.deg (suc k)) d → ∀ l′ dL′ →
          𝒟.tgt (AS.deg (suc k) ∸ 1) (κm k dL d) ≡ κ ((if gd k ==ℕ 0 then suc N else suc (t k)) , l′ , dL′)
    κtm k l dL dg (inj₁ Nk) l′ dL′ = ⊥-elim (no1 (subst (1 ≤_) (deg⊤ k Nk l) dg))
    κtm k l dL dg (inj₂ kN) l′ dL′ =
      trans (cong (λ d → 𝒟.tgt d (F (G′.atom (k * 3 + 1) (kiN k kN) (kiL k kN dL)))) (cong (_∸ 1) (gΣk k kN)))
        (bt k kN l dL (gd k) refl l′ dL′)

    κt : ∀ g (dg : 1 ≤ FO.degG g) → 𝒟.tgt (FO.degG g ∸ 1) (κ g) ≡ κ (FO.tG g dg)
    κt (zero  , _ , _)  dg = ⊥-elim (no1 (subst (1 ≤_) deg⊥ dg))
    κt (suc k , l , dL) dg = κtm k l dL dg (≤-dec N k) (fst (snd (FO.tG (suc k , l , dL) dg))) (snd (snd (FO.tG (suc k , l , dL) dg)))

    -- The factorisation G with G ∘ ν(q) = F.
    G : Functor Sus𝒞 𝒟
    G = FO.Free.functor 𝒟 κ dimκ κs κt

    G-gen : ∀ g → Functor.F G (GS.atom (fst g) (fst (snd g)) (snd (snd g))) ≡ κ g
    G-gen = FO.Free.functor-gen 𝒟 κ dimκ κs κt

    private
      gs = Basis.gdeg K.basis

      atom-eq : ∀ {a a′} → a ≡ a′ → ∀ aN aL aN′ aL′ → G′.atom a aN aL ≡ G′.atom a′ aN′ aL′
      atom-eq refl aN aL aN′ aL′ = ≡-cell K′ L refl

      GF = Functor.F G
      qF = Functor.F νq

      ag-end : ∀ a aN aL → Σ Bool (λ b → Σ Nat (λ k → (k < N) × (a ≡ CE.o b k))) →
               GF (qF (G′.atom a aN aL)) ≡ F (G′.atom a aN aL)
      ag-end a aN aL (b , k , kN , e) =
        trans (cong (λ c → GF (qF c)) (atom-eq e aN aL oN oL))
          (trans (cong GF w)
            (trans (G-gen (CE.ib b , ibN b , ibL b))
              (trans (κ-ib b (ibN b) (ibL b))
                (sym (trans (F-at Φ e aN aL oN oL) (ends b k kN oN oL))))))
        where
        oN = CE.o-N b k kN
        oL = subst (λ i → A′.deg i ≤ L) e aL
        w : qF (G′.atom (CE.o b k) oN oL) ≡ GS.atom (CE.ib b) (ibN b) (ibL b)
        w = ≡-cell KS L (CE.atom-end L b k kN)

      ag-mid : ∀ a aN aL → Σ Nat (λ k → Σ Nat (λ r → (k < N) × ((r < 3) × (a ≡ k * 3 + r)))) → EN.E a ≡ false →
               GF (qF (G′.atom a aN aL)) ≡ F (G′.atom a aN aL)
      ag-mid a aN aL (k , r , kN , rl , e) Ea =
        trans (cong (λ c → GF (qF c)) (atom-eq e′ aN aL (kiN k kN) aL′))
          (trans (cong GF w)
            (trans (G-gen (suc k , s≤s (≤-suc kN) , dL′))
              (trans (κ-mid k kN (s≤s (≤-suc kN)) dL′ (kiN k kN) aL′)
                (sym (F-at Φ e′ aN aL (kiN k kN) aL′)))))
        where
        r1 : r ≡ 1
        r1 = slot-mid (even (at 0 gs k)) r rl (trans (sym (EN.E-at k r kN rl)) (trans (cong EN.E (sym e)) Ea))
        e′ : a ≡ k * 3 + 1
        e′ = trans e (cong (k * 3 +_) r1)
        aL′ = subst (λ i → A′.deg i ≤ L) e′ aL
        dL′ = subst (_≤ L) (mid-deg k kN) aL′
        w : qF (G′.atom (k * 3 + 1) (kiN k kN) aL′) ≡ GS.atom (suc k) (s≤s (≤-suc kN)) dL′
        w = ≡-cell KS L (CA.atom-mid L k kN)

      agree′ : ∀ a aN aL v → EN.E a ≡ v → GF (qF (G′.atom a aN aL)) ≡ F (G′.atom a aN aL)
      agree′ a aN aL true  Ea = ag-end a aN aL (EN.E-o a aN Ea)
      agree′ a aN aL false Ea = ag-mid a aN aL (EN.pos a aN) Ea

    factors : ∀ x → Functor.F (G ∘F νq) x ≡ F x
    factors = G′.uniqueness (toGen (G ∘F νq)) Φg (λ a aN aL → agree′ a aN aL (EN.E a) refl)

    -- The existence statement.
    exists : Σ (Functor Sus𝒞 𝒟) (λ G → ∀ x → Functor.F (G ∘F νq) x ≡ F x)
    exists = G , factors

  ----------------------------------------------------------------------
  -- Uniqueness, once D has a generator.

  unique : 0 < N → (G G′ : Functor Sus𝒞 𝒟) →
           (∀ x → Functor.F G (Functor.F νq x) ≡ Functor.F G′ (Functor.F νq x)) →
           ∀ y → Functor.F G y ≡ Functor.F G′ y
  unique N1 G G′ hyp = FO.unique G G′ h
    where
    oL : ∀ b → A′.deg (CE.o b 0) ≤ L
    oL b = subst (_≤ L) (sym (trans (CE.deg-o b 0 N1) (gd0 N1))) z≤n
    via : ∀ x y → Functor.F νq x ≡ y → Functor.F G y ≡ Functor.F G′ y
    via x y w = trans (cong (Functor.F G) (sym w)) (trans (hyp x) (cong (Functor.F G′) w))
    hm : ∀ k (l : suc k < suc (suc N)) dL → (N ≤ k) ⊎ (k < N) →
         Functor.F G (GS.atom (suc k) l dL) ≡ Functor.F G′ (GS.atom (suc k) l dL)
    hm k l dL (inj₁ Nk) =
      via (G′.atom (CE.o false 0) (CE.o-N false 0 N1) (oL false)) (GS.atom (suc k) l dL)
          (≡-cell KS L (trans (CE.atom-end L false 0 N1) (cong (λ i → AS.atomT L (suc i)) (sym k≡N))))
      where
      ≤-pred′ : ∀ {a b} → suc (suc a) ≤ suc (suc b) → a ≤ b
      ≤-pred′ (s≤s (s≤s l)) = l
      k≡N : k ≡ N
      k≡N = ≤-antisym (≤-pred′ l) Nk
    hm k l dL (inj₂ kN) =
      via (G′.atom (k * 3 + 1) (kiN k kN) (subst (_≤ L) (sym (mid-deg k kN)) dL)) (GS.atom (suc k) l dL)
          (≡-cell KS L (CA.atom-mid L k kN))
    h : ∀ g → Functor.F G (GS.atom (fst g) (fst (snd g)) (snd (snd g))) ≡ Functor.F G′ (GS.atom (fst g) (fst (snd g)) (snd (snd g)))
    h (zero  , l , dL) =
      via (G′.atom (CE.o true 0) (CE.o-N true 0 N1) (oL true)) (GS.atom 0 l dL) (≡-cell KS L (CE.atom-end L true 0 N1))
    h (suc k , l , dL) = hm k l dL (≤-dec N k)

  ----------------------------------------------------------------------
  -- Conversely, G ∘ ν(q) sends the ends to the points G⟨⊥⟩, G⟨⊤⟩.

  ends-of : (G : Functor Sus𝒞 𝒟) → EndsAt (G ∘F νq) (λ b → Functor.F G (GS.atom (CE.ib b) (ibN b) (ibL b)))
  ends-of G = record
    { P0   = λ b → trans (sym (Functor.F-src G 0 _))
                     (cong (Functor.F G) (subst (λ d → νS.src d (GS.atom (CE.ib b) (ibN b) (ibL b)) ≡ GS.atom (CE.ib b) (ibN b) (ibL b))
                                                (deg-ib b) (RS.dim-atom (CE.ib b) (ibN b) (ibL b))))
    ; ends = λ b k kN aN aL → cong (Functor.F G) (≡-cell KS L (CE.atom-end L b k kN))
    }
