------------------------------------------------------------------------
-- Ordered globular bases from their data, and suspension (ledger A5,
-- (N3)).
--
-- `GData` is a finite globular presentation with a strong
-- loop-freeness order: generators 0 … N−1 with degrees gd i, and for
-- gd i ≥ 1 a source s i and a target t i of degree gd i − 1 with
-- s i < i < t i and, for gd i ≥ 2, the globular identities
-- s (s i) = s (t i), t (s i) = t (t i).
--
-- `basis D` is the Steiner complex λΓ of this presentation (∂⁻i = s i,
-- ∂⁺i = t i) as a finite basis, and `hyp D : Hyp (basis D)` proves the
-- hypotheses of `Generation` for it: ∂∂ = 0 from the globular
-- identities, degrees, augmentation, the order, and unitality (the
-- atom ⟨i⟩ has the single 0-cells s^{gd i} i and t^{gd i} i at the
-- bottom). `glob-bm`, `glob-bp` are the parameters of `FreeGlob.Glob`,
-- so `FreeGlob` applies to every `GData`.
--
-- `Σ D` is the suspension: new objects ⊥ = 0 and ⊤ = N + 1, and Σi =
-- i + 1 of degree gd i + 1, with s (Σx) = ⊥, t (Σx) = ⊤ for objects x
-- and s (Σi) = Σ (s i), t (Σi) = Σ (t i) otherwise.
--
-- `Wedge` glues the last object of one presentation to the first object
-- of another; `treeG` sends a Batanin tree (pasting diagram) to the
-- wedge of the suspensions of its branches, so every pasting diagram
-- gives an ordered globular presentation, hence λ of it with `Hyp`.
--
-- Examples: the arrow D¹, Σ D¹ and the tree of the 2-globe, whose
-- bases are `BasisCheck.BD²`; the tree of two composable arrows.
------------------------------------------------------------------------
module CaTTExp.Strict.GlobBasis where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; <→≤; ≤-<-⊥; Tri; tri; tri<; tri≡; tri>)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero; +-suc)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.Trees using (Br; node; nil; cons) renaming (LT to Tree)

------------------------------------------------------------------------
-- Vectors from functions.

tab : ∀ {A : Set} m → (Nat → A) → Nat → Vec A m
tab zero    f j = []
tab (suc m) f j = f j ∷ tab m f (suc j)

at-tab : ∀ {A : Set} {m} (d : A) (f : Nat → A) j i → i < m → at d (tab m f j) i ≡ f (i + j)
at-tab {m = suc m} d f j zero    _       = refl
at-tab {m = suc m} d f j (suc i) (s≤s l) = trans (at-tab d f (suc j) i l) (cong f (+-suc i j))

at-tab0 : ∀ {A : Set} {m} (d : A) (f : Nat → A) i → i < m → at d (tab m f 0) i ≡ f i
at-tab0 d f i l = trans (at-tab d f 0 i l) (cong f (+-zero i))

vextV : ∀ {A : Set} {m} (d : A) (xs ys : Vec A m) → (∀ i → i < m → at d xs i ≡ at d ys i) → xs ≡ ys
vextV d []       []       h = refl
vextV d (x ∷ xs) (y ∷ ys) h = cong₂ _∷_ (h 0 (s≤s z≤n)) (vextV d xs ys (λ i l → h (suc i) (s≤s l)))

private
  at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
  at-out d []       i       _       = refl
  at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

  ==-refl′ : ∀ n → (n ==ℕ n) ≡ true
  ==-refl′ zero    = refl
  ==-refl′ (suc n) = ==-refl′ n

  ==-ne : ∀ m n → (m ≡ n → ⊥) → (m ==ℕ n) ≡ false
  ==-ne zero    zero    ne = ⊥-elim (ne refl)
  ==-ne zero    (suc n) ne = refl
  ==-ne (suc m) zero    ne = refl
  ==-ne (suc m) (suc n) ne = ==-ne m n (λ e → ne (cong suc e))

  1≢0 : ∀ {n} → suc n ≡ 0 → ⊥
  1≢0 ()

  lin-unit : ∀ {M m} i → i < m → (vs : Vec (Vec Nat M) m) → lin (unit {m} i) vs ≡ at 0c vs i
  lin-unit {M} {suc m} zero    _       (v ∷ vs) =
    trans (cong₂ _+c_ (trans (+c-comm v 0c) (+c-id v)) (lin-0 vs)) (trans (+c-comm v 0c) (+c-id v))
  lin-unit {M} {suc m} (suc i) (s≤s l) (v ∷ vs) = trans (+c-id (lin (unit {m} i) vs)) (lin-unit i l vs)

  prj-unit : ∀ {m} (gs : Vec Nat m) k j → k < m → at 0 gs k ≡ j → prj j gs (unit k) ≡ unit k
  prj-unit (g ∷ gs) zero    j _       e rewrite e | ==-refl′ j = cong (1 ∷_) (prj-0 j gs)
  prj-unit (g ∷ gs) (suc k) j (s≤s l) e = cong₂ _∷_ (if-z (g ==ℕ j)) (prj-unit gs k j l e)
    where
    if-z : ∀ b → (if b then 0 else 0) ≡ 0
    if-z true  = refl
    if-z false = refl

  augm-unit : ∀ {m} (gs : Vec Nat m) k → k < m → at 0 gs k ≡ 0 → augm gs (unit k) ≡ 1
  augm-unit (g ∷ gs) zero    _       e rewrite e = cong (1 +_) (augm-0′ gs)
    where
    augm-0′ : ∀ {m} (gs : Vec Nat m) → augm gs 0c ≡ 0
    augm-0′ []       = refl
    augm-0′ (g ∷ gs) with g ==ℕ 0
    ... | true  = augm-0′ gs
    ... | false = augm-0′ gs
  augm-unit (g ∷ gs) (suc k) (s≤s l) e with g ==ℕ 0
  ... | true  = augm-unit gs k l e
  ... | false = augm-unit gs k l e

  at-other : ∀ {m} k g → (k ≡ g → ⊥) → at0 (unit {m} k) g ≡ 0
  at-other {m} k g ne with tri k g
  ... | tri< l = unit-Lo {m} k g l
  ... | tri≡ e = ⊥-elim (ne e)
  ... | tri> l = unit-Hi {m} k g l

  0∸′ : ∀ n → 0 ∸ n ≡ 0
  0∸′ zero    = refl
  0∸′ (suc n) = refl

  unit∸ : ∀ {m} a b → (a ≡ b → ⊥) → unit {m} a ∸c unit b ≡ unit a
  unit∸ {m} a b ne = vext _ _ λ d → trans (at-∸c (unit {m} a) (unit {m} b) d) (go d)
    where
    go : ∀ d → at0 (unit {m} a) d ∸ at0 (unit {m} b) d ≡ at0 (unit {m} a) d
    go d with tri b d
    ... | tri≡ refl = trans (cong (_∸ at0 (unit {m} b) b) (at-other {m} a b ne))
                        (trans (0∸′ (at0 (unit {m} b) b)) (sym (at-other {m} a b ne)))
    ... | tri< l = cong (at0 (unit {m} a) d ∸_) (unit-Lo {m} b d l)
    ... | tri> l = cong (at0 (unit {m} a) d ∸_) (unit-Hi {m} b d l)

------------------------------------------------------------------------
-- Globular data.

record GData : Set where
  field
    N    : Nat
    gd   : Nat → Nat
    s t  : Nat → Nat
    sN   : ∀ i → i < N → 1 ≤ gd i → s i < N
    tN   : ∀ i → i < N → 1 ≤ gd i → t i < N
    ds   : ∀ i → i < N → 1 ≤ gd i → gd (s i) ≡ gd i ∸ 1
    dt   : ∀ i → i < N → 1 ≤ gd i → gd (t i) ≡ gd i ∸ 1
    s-lt : ∀ i → i < N → 1 ≤ gd i → s i < i
    t-gt : ∀ i → i < N → 1 ≤ gd i → i < t i
    gss  : ∀ i → i < N → 2 ≤ gd i → s (s i) ≡ s (t i)
    gtt  : ∀ i → i < N → 2 ≤ gd i → t (s i) ≡ t (t i)

module GB (D : GData) where
  open GData D

  bd : (Nat → Nat) → Nat → Vec Nat N
  bd f i = if gd i ==ℕ 0 then 0c else unit (f i)

  basis : Basis N
  basis = record { gdeg = tab N gd 0 ; bplus = tab N (bd t) 0 ; bminus = tab N (bd s) 0 }

  open Basis basis

  private
    dp dm : Vec Nat N → Vec Nat N
    dp = dP basis
    dm = dM basis

  gdeg-at : ∀ i → i < N → at 0 gdeg i ≡ gd i
  gdeg-at i l = at-tab0 0 gd i l

  bp-at : ∀ i → i < N → at 0c bplus i ≡ bd t i
  bp-at i l = at-tab0 0c (bd t) i l

  bm-at : ∀ i → i < N → at 0c bminus i ≡ bd s i
  bm-at i l = at-tab0 0c (bd s) i l

  private
    bd-pos : ∀ f i → 1 ≤ gd i → bd f i ≡ unit (f i)
    bd-pos f i p with gd i
    ... | suc _ = refl

    bd-0 : ∀ f i → gd i ≡ 0 → bd f i ≡ 0c
    bd-0 f i e rewrite e = refl

    pos : ∀ {d} → 1 ≤ d → suc (d ∸ 1) ≡ d
    pos {suc d} _ = refl

  glob-bm : ∀ i → i < N → 1 ≤ at 0 gdeg i → at 0c bminus i ≡ unit (s i)
  glob-bm i l p = trans (bm-at i l) (bd-pos s i (subst (1 ≤_) (gdeg-at i l) p))

  glob-bp : ∀ i → i < N → 1 ≤ at 0 gdeg i → at 0c bplus i ≡ unit (t i)
  glob-bp i l p = trans (bp-at i l) (bd-pos t i (subst (1 ≤_) (gdeg-at i l) p))

  ----------------------------------------------------------------------
  -- ∂∂ = 0.

  private
    col : ∀ i → i < N → lin (bd t i) bplus +c lin (bd s i) bminus ≡ lin (bd s i) bplus +c lin (bd t i) bminus
    col i l with gd i in e
    ... | zero = refl
    ... | suc j =
      trans (cong₂ _+c_ (trans (lin-unit (t i) tl bplus) (bp-at (t i) tl)) (trans (lin-unit (s i) sl bminus) (bm-at (s i) sl)))
      (trans (inner j dti dsi e)
      (sym (cong₂ _+c_ (trans (lin-unit (s i) sl bplus) (bp-at (s i) sl)) (trans (lin-unit (t i) tl bminus) (bm-at (t i) tl)))))
      where
      p : 1 ≤ gd i
      p = subst (1 ≤_) (sym e) (s≤s z≤n)
      tl = tN i l p
      sl = sN i l p
      dti : gd (t i) ≡ j
      dti = trans (dt i l p) (cong (_∸ 1) e)
      dsi : gd (s i) ≡ j
      dsi = trans (ds i l p) (cong (_∸ 1) e)
      inner : ∀ j → gd (t i) ≡ j → gd (s i) ≡ j → gd i ≡ suc j → bd t (t i) +c bd s (s i) ≡ bd t (s i) +c bd s (t i)
      inner zero    et es _  = trans (cong₂ _+c_ (bd-0 t (t i) et) (bd-0 s (s i) es)) (sym (cong₂ _+c_ (bd-0 t (s i) es) (bd-0 s (t i) et)))
      inner (suc j) et es e2 =
        let p2 : 2 ≤ gd i
            p2 = subst (2 ≤_) (sym e2) (s≤s (s≤s z≤n))
            pt : 1 ≤ gd (t i)
            pt = subst (1 ≤_) (sym et) (s≤s z≤n)
            ps : 1 ≤ gd (s i)
            ps = subst (1 ≤_) (sym es) (s≤s z≤n)
        in trans (cong₂ _+c_ (bd-pos t (t i) pt) (bd-pos s (s i) ps))
           (trans (cong₂ (λ a b → unit a +c unit b) (sym (gtt i l p2)) (gss i l p2))
                  (sym (cong₂ _+c_ (bd-pos t (s i) ps) (bd-pos s (t i) pt))))

  DD-ok : DD basis
  DD-ok = vextV 0c _ _ λ i l →
    trans (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV (λ v → lin v bplus) bplus) (mapV (λ v → lin v bminus) bminus) i)
    (trans (cong₂ _+c_ (trans (at-map (λ v → lin v bplus) 0c 0c (lin-0 bplus) bplus i) (cong (λ v → lin v bplus) (bp-at i l)))
                       (trans (at-map (λ v → lin v bminus) 0c 0c (lin-0 bminus) bminus i) (cong (λ v → lin v bminus) (bm-at i l))))
    (trans (col i l)
    (sym (trans (at-zip _+c_ 0c 0c 0c (+c-id 0c) (mapV (λ v → lin v bplus) bminus) (mapV (λ v → lin v bminus) bplus) i)
              (cong₂ _+c_ (trans (at-map (λ v → lin v bplus) 0c 0c (lin-0 bplus) bminus i) (cong (λ v → lin v bplus) (bm-at i l)))
                          (trans (at-map (λ v → lin v bminus) 0c 0c (lin-0 bminus) bplus i) (cong (λ v → lin v bminus) (bp-at i l))))))))

  ----------------------------------------------------------------------
  -- Degrees, order, augmentation.

  DegP-ok : DegP basis
  DegP-ok = vextV 0c _ _ λ i l →
    trans (at-zip (degFix basis) 0 0c 0c refl gdeg bplus i)
          (trans (cong₂ (degFix basis) (gdeg-at i l) (bp-at i l)) (trans (go i l) (sym (bp-at i l))))
    where
    go : ∀ i → i < N → degFix basis (gd i) (bd t i) ≡ bd t i
    go i l with gd i in e
    ... | zero  = refl
    ... | suc j = prj-unit gdeg (t i) j tl (trans (gdeg-at (t i) tl) (trans (dt i l p) (cong (_∸ 1) e)))
      where
      p : 1 ≤ gd i
      p = subst (1 ≤_) (sym e) (s≤s z≤n)
      tl = tN i l p

  DegM-ok : DegM basis
  DegM-ok = vextV 0c _ _ λ i l →
    trans (at-zip (degFix basis) 0 0c 0c refl gdeg bminus i)
          (trans (cong₂ (degFix basis) (gdeg-at i l) (bm-at i l)) (trans (go i l) (sym (bm-at i l))))
    where
    go : ∀ i → i < N → degFix basis (gd i) (bd s i) ≡ bd s i
    go i l with gd i in e
    ... | zero  = refl
    ... | suc j = prj-unit gdeg (s i) j sl (trans (gdeg-at (s i) sl) (trans (ds i l p) (cong (_∸ 1) e)))
      where
      p : 1 ≤ gd i
      p = subst (1 ≤_) (sym e) (s≤s z≤n)
      sl = sN i l p

  ordm-ok : ∀ i d → i ≤ d → at0 (at 0c bminus i) d ≡ 0
  ordm-ok i d q with ≤-dec N i
  ... | inj₁ Ni = trans (cong (λ v → at0 v d) (at-out 0c bminus i Ni)) (at-0c {N} d)
  ... | inj₂ iN = trans (cong (λ v → at0 v d) (bm-at i iN)) (go (gd i) refl)
    where
    go : ∀ g → gd i ≡ g → at0 (bd s i) d ≡ 0
    go zero    e = trans (cong (λ v → at0 v d) (bd-0 s i e)) (at-0c {N} d)
    go (suc g) e = let p = subst (1 ≤_) (sym e) (s≤s z≤n) in
      trans (cong (λ v → at0 v d) (bd-pos s i p)) (unit-Lo {N} (s i) d (≤-trans (s-lt i iN p) q))

  ordp-ok : ∀ i d → d ≤ i → at0 (at 0c bplus i) d ≡ 0
  ordp-ok i d q with ≤-dec N i
  ... | inj₁ Ni = trans (cong (λ v → at0 v d) (at-out 0c bplus i Ni)) (at-0c {N} d)
  ... | inj₂ iN = trans (cong (λ v → at0 v d) (bp-at i iN)) (go (gd i) refl)
    where
    go : ∀ g → gd i ≡ g → at0 (bd t i) d ≡ 0
    go zero    e = trans (cong (λ v → at0 v d) (bd-0 t i e)) (at-0c {N} d)
    go (suc g) e = let p = subst (1 ≤_) (sym e) (s≤s z≤n) in
      trans (cong (λ v → at0 v d) (bd-pos t i p)) (unit-Hi {N} (t i) d (≤-trans (s≤s q) (t-gt i iN p)))

  Aug1-ok : Aug1 basis
  Aug1-ok = vextV 0 _ _ λ i l →
    trans (at-zip (augFix basis) 0 0c 0 refl gdeg bplus i)
    (trans (cong₂ (augFix basis) (gdeg-at i l) (bp-at i l))
    (trans (go i l)
    (sym (trans (at-zip (augFix basis) 0 0c 0 refl gdeg bminus i) (cong₂ (augFix basis) (gdeg-at i l) (bm-at i l))))))
    where
    go : ∀ i → i < N → augFix basis (gd i) (bd t i) ≡ augFix basis (gd i) (bd s i)
    go i l with gd i in e
    ... | zero        = refl
    ... | suc (suc j) = refl
    ... | suc zero    =
      trans (augm-unit gdeg (t i) tl (trans (gdeg-at (t i) tl) (trans (dt i l p) (cong (_∸ 1) e))))
            (sym (augm-unit gdeg (s i) sl (trans (gdeg-at (s i) sl) (trans (ds i l p) (cong (_∸ 1) e)))))
      where
      p : 1 ≤ gd i
      p = subst (1 ≤_) (sym e) (s≤s z≤n)
      tl = tN i l p
      sl = sN i l p

  ----------------------------------------------------------------------
  -- Unitality.

  open Atom basis using (entK; step)

  private
    st-ne : ∀ i → i < N → 1 ≤ gd i → s i ≡ t i → ⊥
    st-ne i l p e = ≤-<-⊥ (≤-trans (≤-of (sym e)) (<→≤ (s-lt i l p))) (t-gt i l p)
      where
      ≤-of : ∀ {a b} → a ≡ b → a ≤ b
      ≤-of refl = ≤-refl _

    step-unit : ∀ i → i < N → 1 ≤ gd i → step (unit i , unit i) ≡ (unit (s i) , unit (t i))
    step-unit i l p =
      let p′ = subst (1 ≤_) (sym (gdeg-at i l)) p in
      cong₂ _,_ (trans (cong₂ _∸c_ (trans (lin-unit i l bminus) (glob-bm i l p′)) (trans (lin-unit i l bplus) (glob-bp i l p′)))
                       (unit∸ (s i) (t i) (st-ne i l p)))
                (trans (cong₂ _∸c_ (trans (lin-unit i l bplus) (glob-bp i l p′)) (trans (lin-unit i l bminus) (glob-bm i l p′)))
                       (unit∸ (t i) (s i) (λ e → st-ne i l p (sym e))))

  claim : ∀ i → i < N → 1 ≤ gd i → ∀ k → entK i (suc k) ≡ (fst (entK (s i) k) , snd (entK (t i) k))
  claim i l p zero    = step-unit i l p
  claim i l p (suc k) = cong step (claim i l p k)

  private
    U : ∀ d i → i < N → gd i ≡ d → (augm gdeg (fst (entK i d)) ≡ 1) × (augm gdeg (snd (entK i d)) ≡ 1)
    U zero    i l e = let a = augm-unit gdeg i l (trans (gdeg-at i l) e) in a , a
    U (suc d) i l e =
      let p  = subst (1 ≤_) (sym e) (s≤s z≤n)
          sl = sN i l p
          tl = tN i l p
          c  = claim i l p d
      in trans (cong (λ x → augm gdeg (fst x)) c) (fst (U d (s i) sl (trans (ds i l p) (cong (_∸ 1) e)))) ,
         trans (cong (λ x → augm gdeg (snd x)) c) (snd (U d (t i) tl (trans (dt i l p) (cong (_∸ 1) e))))

  hyp : Hyp basis
  hyp = record
    { dd = dd-from basis DD-ok
    ; deg-dp = deg-from basis bplus DegP-ok
    ; deg-dm = deg-from basis bminus DegM-ok
    ; ordm = ordm-ok
    ; ordp = ordp-ok
    ; aug1 = aug-from basis Aug1-ok
    ; unital = λ i l → U (at 0 gdeg i) i l (sym (gdeg-at i l))
    }

------------------------------------------------------------------------
-- Suspension.

private
  <ℕ-sound : ∀ m n → (m <ℕ n) ≡ true → m < n
  <ℕ-sound zero    (suc n) e = s≤s z≤n
  <ℕ-sound (suc m) (suc n) e = s≤s (<ℕ-sound m n e)
  <ℕ-sound zero    zero    ()
  <ℕ-sound (suc m) zero    ()

  two2 : ∀ {x} → 2 ≤ suc x → x ≡ 0 → ⊥
  two2 (s≤s ()) refl

  <ℕ-irr : ∀ n → (n <ℕ n) ≡ false
  <ℕ-irr zero    = refl
  <ℕ-irr (suc n) = <ℕ-irr n

  <ℕ-complete : ∀ m n → m < n → (m <ℕ n) ≡ true
  <ℕ-complete zero    (suc n) _       = refl
  <ℕ-complete (suc m) (suc n) (s≤s l) = <ℕ-complete m n l

Σg : GData → GData
Σg D = record
  { N = suc (suc N) ; gd = gdΣ ; s = sΣ ; t = tΣ
  ; sN = sN′ ; tN = tN′ ; ds = ds′ ; dt = dt′ ; s-lt = s-lt′ ; t-gt = t-gt′ ; gss = gss′ ; gtt = gtt′ }
  where
  open GData D
  gdΣ sΣ tΣ : Nat → Nat
  gdΣ zero    = 0
  gdΣ (suc k) = if k <ℕ N then suc (gd k) else 0
  sΣ zero    = 0
  sΣ (suc k) = if gd k ==ℕ 0 then 0 else suc (s k)
  tΣ zero    = 0
  tΣ (suc k) = if gd k ==ℕ 0 then suc N else suc (t k)

  gdΣ-in : ∀ k → k < N → gdΣ (suc k) ≡ suc (gd k)
  gdΣ-in k l rewrite <ℕ-complete k N l = refl

  -- A generator of positive degree in Σ D is Σk for some k < N.
  inner : ∀ k → suc k < suc (suc N) → 1 ≤ gdΣ (suc k) → k < N
  inner k _ p with k <ℕ N in e
  ... | true  = <ℕ-sound k N e
  ... | false = ⊥-elim (absurd p)
    where
    absurd : 1 ≤ 0 → ⊥
    absurd ()

  sN′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → sΣ i < suc (suc N)
  sN′ (suc k) l p with inner k l p
  ... | kN with gd k in e
  ... | zero  = s≤s z≤n
  ... | suc j = s≤s (≤-suc (sN k kN (subst (1 ≤_) (sym e) (s≤s z≤n))))

  tN′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → tΣ i < suc (suc N)
  tN′ (suc k) l p with inner k l p
  ... | kN with gd k in e
  ... | zero  = ≤-refl _
  ... | suc j = s≤s (≤-suc (tN k kN (subst (1 ≤_) (sym e) (s≤s z≤n))))

  ds′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → gdΣ (sΣ i) ≡ gdΣ i ∸ 1
  ds′ (suc k) l p with inner k l p
  ... | kN rewrite gdΣ-in k kN with gd k in e
  ... | zero  = refl
  ... | suc j = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (gdΣ-in (s k) (sN k kN p′)) (cong suc (trans (ds k kN p′) (cong (_∸ 1) e)))

  dt′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → gdΣ (tΣ i) ≡ gdΣ i ∸ 1
  dt′ (suc k) l p with inner k l p
  ... | kN rewrite gdΣ-in k kN with gd k in e
  ... | zero  rewrite <ℕ-irr N = refl
  ... | suc j = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (gdΣ-in (t k) (tN k kN p′)) (cong suc (trans (dt k kN p′) (cong (_∸ 1) e)))

  s-lt′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → sΣ i < i
  s-lt′ (suc k) l p with inner k l p
  ... | kN with gd k in e
  ... | zero  = s≤s z≤n
  ... | suc j = s≤s (s-lt k kN (subst (1 ≤_) (sym e) (s≤s z≤n)))

  t-gt′ : ∀ i → i < suc (suc N) → 1 ≤ gdΣ i → i < tΣ i
  t-gt′ (suc k) l p with inner k l p
  ... | kN with gd k in e
  ... | zero  = s≤s kN
  ... | suc j = s≤s (t-gt k kN (subst (1 ≤_) (sym e) (s≤s z≤n)))

  gss′ : ∀ i → i < suc (suc N) → 2 ≤ gdΣ i → sΣ (sΣ i) ≡ sΣ (tΣ i)
  gss′ (suc k) l p with inner k l (≤-trans (≤-suc (≤-refl 1)) p)
  ... | kN rewrite gdΣ-in k kN with gd k in e
  ...   | zero        = ⊥-elim (two2 p refl)
  ...   | suc zero    = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (cong (λ g → if g ==ℕ 0 then 0 else suc (s (s k))) (trans (ds k kN p′) (cong (_∸ 1) e)))
          (sym (cong (λ g → if g ==ℕ 0 then 0 else suc (s (t k))) (trans (dt k kN p′) (cong (_∸ 1) e))))
  ...   | suc (suc j) = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (cong (λ g → if g ==ℕ 0 then 0 else suc (s (s k))) (trans (ds k kN p′) (cong (_∸ 1) e)))
    (trans (cong suc (gss k kN (subst (2 ≤_) (sym e) (s≤s (s≤s z≤n)))))
           (sym (cong (λ g → if g ==ℕ 0 then 0 else suc (s (t k))) (trans (dt k kN p′) (cong (_∸ 1) e)))))

  gtt′ : ∀ i → i < suc (suc N) → 2 ≤ gdΣ i → tΣ (sΣ i) ≡ tΣ (tΣ i)
  gtt′ (suc k) l p with inner k l (≤-trans (≤-suc (≤-refl 1)) p)
  ... | kN rewrite gdΣ-in k kN with gd k in e
  ...   | zero        = ⊥-elim (two2 p refl)
  ...   | suc zero    = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (cong (λ g → if g ==ℕ 0 then suc N else suc (t (s k))) (trans (ds k kN p′) (cong (_∸ 1) e)))
          (sym (cong (λ g → if g ==ℕ 0 then suc N else suc (t (t k))) (trans (dt k kN p′) (cong (_∸ 1) e))))
  ...   | suc (suc j) = let p′ = subst (1 ≤_) (sym e) (s≤s z≤n) in
    trans (cong (λ g → if g ==ℕ 0 then suc N else suc (t (s k))) (trans (ds k kN p′) (cong (_∸ 1) e)))
    (trans (cong suc (gtt k kN (subst (2 ≤_) (sym e) (s≤s (s≤s z≤n)))))
           (sym (cong (λ g → if g ==ℕ 0 then suc N else suc (t (t k))) (trans (dt k kN p′) (cong (_∸ 1) e)))))

------------------------------------------------------------------------
-- `FreeGlob` for every globular presentation.

module FreeOn (D : GData) (L : Nat) where
  open GData D
  open GB D

  private
    up : ∀ i → i < N → 1 ≤ Atom.deg basis i → 1 ≤ gd i
    up i l p = subst (1 ≤_) (gdeg-at i l) p

  open import CaTTExp.Strict.FreeGlob using (module Glob)

  open Glob basis hyp L s t glob-bm glob-bp
         (λ i l p → sN i l (up i l p)) (λ i l p → tN i l (up i l p))
         (λ i l p → trans (gdeg-at (s i) (sN i l (up i l p))) (trans (ds i l (up i l p)) (cong (_∸ 1) (sym (gdeg-at i l)))))
         (λ i l p → trans (gdeg-at (t i) (tN i l (up i l p))) (trans (dt i l (up i l p)) (cong (_∸ 1) (sym (gdeg-at i l)))))
    public

------------------------------------------------------------------------
-- Examples.

-- The arrow x → f → y, listed x, f, y.
D¹ : GData
D¹ = record
  { N = 3 ; gd = g ; s = λ _ → 0 ; t = λ _ → 2
  ; sN = λ { (suc zero) _ _ → s≤s z≤n ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; tN = λ { (suc zero) _ _ → s≤s (s≤s (s≤s z≤n)) ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; ds = λ { (suc zero) _ _ → refl ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; dt = λ { (suc zero) _ _ → refl ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; s-lt = λ { (suc zero) _ _ → s≤s z≤n ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; t-gt = λ { (suc zero) _ _ → s≤s (s≤s z≤n) ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; gss = λ { (suc zero) _ (s≤s ()) ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  ; gtt = λ { (suc zero) _ (s≤s ()) ; zero _ () ; (suc (suc zero)) _ () ; (suc (suc (suc _))) (s≤s (s≤s (s≤s ()))) _ }
  }
  where
  g : Nat → Nat
  g zero          = 0
  g (suc zero)    = 1
  g (suc (suc _)) = 0

D¹-basis : GB.basis D¹ ≡ BD¹
D¹-basis = refl

-- The suspension of the arrow is the 2-globe.
ΣD¹-basis : GB.basis (Σg D¹) ≡ BD²
ΣD¹-basis = refl

------------------------------------------------------------------------
-- Wedge: glue the last object of D to the first object of D′.
--
-- With N = M + 1 and N′ = M′ + 1, the wedge has M + M′ + 1 generators:
-- i ≤ M is i in D, and j + M (j ≥ 1) is j in D′; M is both the last
-- generator of D and the first of D′, which must be objects.

private
  +-lt : ∀ {a b} M → a < b → a + M < b + M
  +-lt {a} {b} M l = subst₂ _<_ (+-comm M a) (+-comm M b) (go M l)
    where
    go : ∀ M → a < b → M + a < M + b
    go zero    l = l
    go (suc M) l = s≤s (go M l)
    subst₂ : ∀ {A : Set} (R : A → A → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → R x y → R x′ y′
    subst₂ R refl refl r = r

  +∸ : ∀ j M → (j + M) ∸ M ≡ j
  +∸ j zero    = +-zero j
  +∸ j (suc M) = trans (cong (_∸ suc M) (+-suc j M)) (+∸ j M)

  lt-right : ∀ j M → 1 ≤ j → (j + M <ℕ suc M) ≡ false
  lt-right (suc j) zero    _ = refl
  lt-right (suc j) (suc M) p = trans (cong (_<ℕ suc (suc M)) (+-suc (suc j) M)) (lt-right (suc j) M p)

  lt-left : ∀ i M → i ≤ M → (i <ℕ suc M) ≡ true
  lt-left zero    M       _       = refl
  lt-left (suc i) (suc M) (s≤s l) = lt-left i M l

  bound-right : ∀ j M M′ → j < suc M′ → j + M < suc (M + M′)
  bound-right j M M′ l = subst (j + M <_) (cong suc (+-comm M′ M)) (+-lt M l)

  bound-right′ : ∀ j M M′ → j + M < suc (M + M′) → j < suc M′
  bound-right′ j M M′ l with ≤-dec (suc M′) j
  ... | inj₂ p = p
  ... | inj₁ p = ⊥-elim (≤-<-⊥ (subst (_≤ j + M) (cong suc (+-comm M′ M)) (≤-trans (≤-+r p M) (≤-refl _))) l)
    where
    ≤-+r : ∀ {a b} → a ≤ b → ∀ M → a + M ≤ b + M
    ≤-+r {a} {b} p M = subst₂′ (+-comm M a) (+-comm M b) (go M)
      where
      go : ∀ M → M + a ≤ M + b
      go zero    = p
      go (suc M) = s≤s (go M)
      subst₂′ : ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → x ≤ y → x′ ≤ y′
      subst₂′ refl refl r = r

  split : ∀ i M → (i ≤ M) ⊎ Σ Nat (λ j → (1 ≤ j) × (i ≡ j + M))
  split i M with ≤-dec i M
  ... | inj₁ p = inj₁ p
  ... | inj₂ p = let (k , e) = <-split p in inj₂ (suc k , s≤s z≤n , trans e (+-comm M (suc k)))

module Wedge (D D′ : GData) (M M′ : Nat)
             (eN : GData.N D ≡ suc M) (eN′ : GData.N D′ ≡ suc M′)
             (last0 : GData.gd D M ≡ 0) (first0 : GData.gd D′ 0 ≡ 0) where
  open GData D
  module D′ = GData D′

  gdW sW tW : Nat → Nat
  gdW i = if i <ℕ suc M then gd i else D′.gd (i ∸ M)
  sW  i = if i <ℕ suc M then s i else (D′.s (i ∸ M) + M)
  tW  i = if i <ℕ suc M then t i else (D′.t (i ∸ M) + M)

  gdL : ∀ i → i ≤ M → gdW i ≡ gd i
  gdL i l rewrite lt-left i M l = refl
  sL : ∀ i → i ≤ M → sW i ≡ s i
  sL i l rewrite lt-left i M l = refl
  tL : ∀ i → i ≤ M → tW i ≡ t i
  tL i l rewrite lt-left i M l = refl

  gdR′ : ∀ j → 1 ≤ j → gdW (j + M) ≡ D′.gd j
  gdR′ j p rewrite lt-right j M p = cong D′.gd (+∸ j M)
  sR : ∀ j → 1 ≤ j → sW (j + M) ≡ D′.s j + M
  sR j p rewrite lt-right j M p = cong (λ x → D′.s x + M) (+∸ j M)
  tR : ∀ j → 1 ≤ j → tW (j + M) ≡ D′.t j + M
  tR j p rewrite lt-right j M p = cong (λ x → D′.t x + M) (+∸ j M)

  gdR : ∀ j → gdW (j + M) ≡ D′.gd j
  gdR zero    = trans (gdL M (≤-refl M)) (trans last0 (sym first0))
  gdR (suc j) = gdR′ (suc j) (s≤s z≤n)

  private
    inD : ∀ i → i ≤ M → i < N
    inD i l = subst (i <_) (sym eN) (s≤s l)
    inD′ : ∀ j → j < suc M′ → j < D′.N
    inD′ j l = subst (j <_) (sym eN′) l
    leM : ∀ i → i < N → i ≤ M
    leM i l with subst (i <_) eN l
    ... | s≤s p = p
    ltM′ : ∀ j → j < D′.N → j < suc M′
    ltM′ j l = subst (j <_) eN′ l
    pos′ : ∀ j → 1 ≤ D′.gd j → 1 ≤ j
    pos′ zero    p = ⊥-elim (absurd (subst (1 ≤_) first0 p))
      where
      absurd : 1 ≤ 0 → ⊥
      absurd ()
    pos′ (suc j) p = s≤s z≤n
    NW = suc (M + M′)
    jN : ∀ j → j + M < NW → j < D′.N
    jN j l = inD′ j (bound-right′ j M M′ l)
    ≤-of : ∀ {a b} → a ≡ b → a ≤ b
    ≤-of refl = ≤-refl _
    toW : ∀ i → i ≤ M → i < NW
    toW i l = s≤s (≤-trans l (≤-+ M M′))
      where
      ≤-+ : ∀ a b → a ≤ a + b
      ≤-+ zero    b = z≤n
      ≤-+ (suc a) b = s≤s (≤-+ a b)

  wedge : GData
  wedge = record
    { N = NW ; gd = gdW ; s = sW ; t = tW
    ; sN = sN′ ; tN = tN′ ; ds = ds′ ; dt = dt′ ; s-lt = s-lt′ ; t-gt = t-gt′ ; gss = gss′ ; gtt = gtt′ }
    where
    sN′ : ∀ i → i < NW → 1 ≤ gdW i → sW i < NW
    sN′ i l p with split i M
    ... | inj₁ q = subst (_< NW) (sym (sL i q)) (toW (s i) (leM (s i) (sN i (inD i q) (subst (1 ≤_) (gdL i q) p))))
    ... | inj₂ (j , q , refl) =
      let jl = jN j l ; p′ = subst (1 ≤_) (gdR′ j q) p in
      subst (_< NW) (sym (sR j q)) (bound-right (D′.s j) M M′ (ltM′ (D′.s j) (D′.sN j jl p′)))

    tN′ : ∀ i → i < NW → 1 ≤ gdW i → tW i < NW
    tN′ i l p with split i M
    ... | inj₁ q = subst (_< NW) (sym (tL i q)) (toW (t i) (leM (t i) (tN i (inD i q) (subst (1 ≤_) (gdL i q) p))))
    ... | inj₂ (j , q , refl) =
      let jl = jN j l ; p′ = subst (1 ≤_) (gdR′ j q) p in
      subst (_< NW) (sym (tR j q)) (bound-right (D′.t j) M M′ (ltM′ (D′.t j) (D′.tN j jl p′)))

    ds′ : ∀ i → i < NW → 1 ≤ gdW i → gdW (sW i) ≡ gdW i ∸ 1
    ds′ i l p with split i M
    ... | inj₁ q = let iN = inD i q ; p′ = subst (1 ≤_) (gdL i q) p in
      trans (cong gdW (sL i q)) (trans (gdL (s i) (leM (s i) (sN i iN p′))) (trans (ds i iN p′) (cong (_∸ 1) (sym (gdL i q)))))
    ... | inj₂ (j , q , refl) = let jl = jN j l ; p′ = subst (1 ≤_) (gdR′ j q) p in
      trans (cong gdW (sR j q)) (trans (gdR (D′.s j)) (trans (D′.ds j jl p′) (cong (_∸ 1) (sym (gdR′ j q)))))

    dt′ : ∀ i → i < NW → 1 ≤ gdW i → gdW (tW i) ≡ gdW i ∸ 1
    dt′ i l p with split i M
    ... | inj₁ q = let iN = inD i q ; p′ = subst (1 ≤_) (gdL i q) p in
      trans (cong gdW (tL i q)) (trans (gdL (t i) (leM (t i) (tN i iN p′))) (trans (dt i iN p′) (cong (_∸ 1) (sym (gdL i q)))))
    ... | inj₂ (j , q , refl) = let jl = jN j l ; p′ = subst (1 ≤_) (gdR′ j q) p in
      trans (cong gdW (tR j q)) (trans (gdR (D′.t j)) (trans (D′.dt j jl p′) (cong (_∸ 1) (sym (gdR′ j q)))))

    s-lt′ : ∀ i → i < NW → 1 ≤ gdW i → sW i < i
    s-lt′ i l p with split i M
    ... | inj₁ q = subst (_< i) (sym (sL i q)) (s-lt i (inD i q) (subst (1 ≤_) (gdL i q) p))
    ... | inj₂ (j , q , refl) = subst (_< j + M) (sym (sR j q)) (+-lt M (D′.s-lt j (jN j l) (subst (1 ≤_) (gdR′ j q) p)))

    t-gt′ : ∀ i → i < NW → 1 ≤ gdW i → i < tW i
    t-gt′ i l p with split i M
    ... | inj₁ q = subst (i <_) (sym (tL i q)) (t-gt i (inD i q) (subst (1 ≤_) (gdL i q) p))
    ... | inj₂ (j , q , refl) = subst (j + M <_) (sym (tR j q)) (+-lt M (D′.t-gt j (jN j l) (subst (1 ≤_) (gdR′ j q) p)))

    -- In degree ≥ 2 the boundaries stay on the same side (and, on the
    -- right, away from the glued object).
    two-one : ∀ {g} → 2 ≤ g → 1 ≤ g
    two-one (s≤s _) = s≤s z≤n
    one-pred : ∀ {g} → 2 ≤ g → 1 ≤ g ∸ 1
    one-pred (s≤s (s≤s _)) = s≤s z≤n

    gss′ : ∀ i → i < NW → 2 ≤ gdW i → sW (sW i) ≡ sW (tW i)
    gss′ i l p with split i M
    ... | inj₁ q = let iN = inD i q ; p2 = subst (2 ≤_) (gdL i q) p ; p1 = two-one p2 in
      trans (cong sW (sL i q)) (trans (sL (s i) (leM (s i) (sN i iN p1)))
      (trans (gss i iN p2) (sym (trans (cong sW (tL i q)) (sL (t i) (leM (t i) (tN i iN p1)))))))
    ... | inj₂ (j , q , refl) =
      let jl = jN j l ; p2 = subst (2 ≤_) (gdR′ j q) p ; p1 = two-one p2
          qs = pos′ (D′.s j) (subst (1 ≤_) (sym (D′.ds j jl p1)) (one-pred p2))
          qt = pos′ (D′.t j) (subst (1 ≤_) (sym (D′.dt j jl p1)) (one-pred p2))
      in trans (cong sW (sR j q)) (trans (sR (D′.s j) qs)
         (trans (cong (_+ M) (D′.gss j jl p2)) (sym (trans (cong sW (tR j q)) (sR (D′.t j) qt)))))

    gtt′ : ∀ i → i < NW → 2 ≤ gdW i → tW (sW i) ≡ tW (tW i)
    gtt′ i l p with split i M
    ... | inj₁ q = let iN = inD i q ; p2 = subst (2 ≤_) (gdL i q) p ; p1 = two-one p2 in
      trans (cong tW (sL i q)) (trans (tL (s i) (leM (s i) (sN i iN p1)))
      (trans (gtt i iN p2) (sym (trans (cong tW (tL i q)) (tL (t i) (leM (t i) (tN i iN p1)))))))
    ... | inj₂ (j , q , refl) =
      let jl = jN j l ; p2 = subst (2 ≤_) (gdR′ j q) p ; p1 = two-one p2
          qs = pos′ (D′.s j) (subst (1 ≤_) (sym (D′.ds j jl p1)) (one-pred p2))
          qt = pos′ (D′.t j) (subst (1 ≤_) (sym (D′.dt j jl p1)) (one-pred p2))
      in trans (cong tW (sR j q)) (trans (tR (D′.s j) qs)
         (trans (cong (_+ M) (D′.gtt j jl p2)) (sym (trans (cong tW (tR j q)) (tR (D′.t j) qt)))))

------------------------------------------------------------------------
-- Batanin trees: a tree is the wedge of the suspensions of its
-- branches, so every Batanin tree (pasting diagram) gives an ordered
-- globular presentation.

point : GData
point = record
  { N = 1 ; gd = λ _ → 0 ; s = λ _ → 0 ; t = λ _ → 0
  ; sN = λ _ _ () ; tN = λ _ _ () ; ds = λ _ _ () ; dt = λ _ _ () ; s-lt = λ _ _ () ; t-gt = λ _ _ ()
  ; gss = λ _ _ () ; gtt = λ _ _ () }

-- A presentation whose first and last generators are objects.
record Pointed : Set where
  field
    G      : GData
    M      : Nat
    eN     : GData.N G ≡ suc M
    first0 : GData.gd G 0 ≡ 0
    last0  : GData.gd G M ≡ 0

ptP : Pointed
ptP = record { G = point ; M = 0 ; eN = refl ; first0 = refl ; last0 = refl }

ΣP : GData → Pointed
ΣP D = record { G = Σg D ; M = suc (GData.N D) ; eN = refl ; first0 = refl ; last0 = l0 }
  where
  l0 : (if GData.N D <ℕ GData.N D then suc (GData.gd D (GData.N D)) else 0) ≡ 0
  l0 rewrite <ℕ-irr (GData.N D) = refl

∨P : Pointed → Pointed → Pointed
∨P P P′ = record
  { G = W.wedge ; M = Pointed.M P + Pointed.M P′ ; eN = refl
  ; first0 = trans (W.gdL 0 z≤n) (Pointed.first0 P)
  ; last0 = trans (cong W.gdW (+-comm (Pointed.M P) (Pointed.M P′))) (trans (W.gdR (Pointed.M P′)) (Pointed.last0 P′)) }
  where
  module W = Wedge (Pointed.G P) (Pointed.G P′) (Pointed.M P) (Pointed.M P′)
                   (Pointed.eN P) (Pointed.eN P′) (Pointed.last0 P) (Pointed.first0 P′)

module _ {A : Set} where
  mutual
    treeP : Tree A → Pointed
    treeP (node _ r) = branchP r

    branchP : Br A → Pointed
    branchP nil          = ptP
    branchP (cons T _ r) = ∨P (ΣP (Pointed.G (treeP T))) (branchP r)

  treeG : Tree A → GData
  treeG T = Pointed.G (treeP T)

-- The 2-globe as a tree: x —f→ y with the 2-cell α : f ⇒ g above f.
private
  T² : Tree Nat
  T² = node 0 (cons (node 1 (cons (node 2 nil) 3 nil)) 4 nil)

tree-D² : GB.basis (treeG T²) ≡ BD²
tree-D² = refl

-- Two composable arrows x → y → z.
private
  T¹¹ : Tree Nat
  T¹¹ = node 0 (cons (node 1 nil) 2 (cons (node 3 nil) 4 nil))

tree-comp : Hyp (GB.basis (treeG T¹¹))
tree-comp = GB.hyp (treeG T¹¹)
