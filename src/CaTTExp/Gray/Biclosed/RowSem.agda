------------------------------------------------------------------------
-- The rows of F.7.4 §2 in a model of the biclosed kernel: the map
-- r : H → B on cells of every dimension, its inverse, and how both
-- commute with faces.  No postulates.
--
-- A k-cell of M at gap g is an operation with dsrc k (nothing at k = 0,
-- ⟦Dᵏ⟧ otherwise) inserted after the first g inputs of M.  For the slot
-- rows (pair, probe, unit) r precomposes with the corolla, whose input
-- position moves past the time slot when the slot is to its left; for
-- the evaluation rows r postcomposes with e^ℓ or e^r.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.RowSem (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.ListOps
open import CaTTExp.Gray.Biclosed.Rows hiding (pos)
open import CaTTExp.Gray.Biclosed.ListLemmas
open Model 𝔐
open import CaTTExp.Gray.Biclosed.ModelFacts 𝔐

------------------------------------------------------------------------
-- Cells

record CellAt (k g : Nat) (M : MTy) (x : V) : Set where
  constructor cellAt
  field
    pre post : List Fm
    sp  : pre ++ post ≡ ins M
    len : length pre ≡ g
    typ : x ∶ ((pre ++ dsrc k ++ post) ▸ out M)
open CellAt public

face-cell : ∀ {k g M x} α → CellAt (suc k) g M x → CellAt k g M (pc x g (δ α k))
face-cell {k} α (cellAt pre post sp refl tx) =
  cellAt pre post sp refl (T-pc {P = pre} {Y = D (suc k)} {Q = post} tx (T-δ α k))

cell-≈ : ∀ {k g M x y} → x ≈ y → CellAt k g M x → CellAt k g M y
cell-≈ p (cellAt pre post sp len tx) = cellAt pre post sp len (∶-≈ p tx)

------------------------------------------------------------------------
-- Small helpers

if-T : ∀ {A : Set} b {x y : A} → T b → (if b then x else y) ≡ x
if-T true _ = refl

if-F : ∀ {A : Set} b {x y : A} → b ≡ false → (if b then x else y) ≡ y
if-F false _ = refl

pc-at₁ : ∀ f {i j} g → i ≡ j → pc f i g ≡ pc f j g
pc-at₁ f g refl = refl

+-one : ∀ n → n + 1 ≡ suc n
+-one zero    = refl
+-one (suc n) = cong suc (+-one n)

-- a + b + c ≡ a + c + b
+-swap₂ : ∀ a b c → a + b + c ≡ a + c + b
+-swap₂ a b c = trans (+-assoc a b c) (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

length-++₃ : ∀ (P Q R : List Fm) → length (P ++ Q ++ R) ≡ length P + length Q + length R
length-++₃ P Q R = trans (length-++ P (Q ++ R)) (trans (cong (length P +_) (length-++ Q R))
                          (sym (+-assoc (length P) (length Q) (length R))))

unC-l-at : ∀ {x P c Q Z i} → x ∶ ((P ++ corOut c ∷ Q) ▸ Z) → length P ≡ i →
           unC c i (pc x i (cor c)) ≈ x
unC-l-at p refl = unC-l p

unC-r-at : ∀ {y P c Q Z i} → y ∶ ((P ++ corIns c ++ Q) ▸ Z) → length P ≡ i →
           pc (unC c i y) i (cor c) ≈ y
unC-r-at p refl = unC-r p

T-unC-at : ∀ {y P c Q Z i} → y ∶ ((P ++ corIns c ++ Q) ▸ Z) → length P ≡ i →
           unC c i y ∶ ((P ++ corOut c ∷ Q) ▸ Z)
T-unC-at p refl = T-unC p

T-pc-at : ∀ {f g P Y Q Z Xs i} → f ∶ ((P ++ Y ∷ Q) ▸ Z) → g ∶ (Xs ▸ Y) → length P ≡ i →
          pc f i g ∶ ((P ++ Xs ++ Q) ▸ Z)
T-pc-at pf pg refl = T-pc pf pg

------------------------------------------------------------------------
-- Slot rows: H = (L, corOut c, R ▸ Z), B = (L, corIns c, R ▸ Z)

cpos : List Fm → Nat → Nat → Nat
cpos L g k = if leq g (length L) then length L + length (dsrc k) else length L

gS : List Fm → Cor → List Fm → Nat → Nat
gS L c R g = sumIns (take g (idTys L ++ (corIns c ▸ corOut c) ∷ idTys R))

T→true : ∀ {b} → T b → b ≡ true
T→true {true} _ = refl

gS-left : ∀ L c R g → T (leq g (length L)) → gS L c R g ≡ g
gS-left L c R g p =
  trans (cong sumIns (take-++ˡ g (idTys L) _ (subst (λ n → T (leq g n)) (sym (length-map _ L)) p)))
  (trans (cong sumIns (take-map _ g L))
  (trans (cong length (concatIns-idTys (take g L))) (length-take g L p)))

gS-right : ∀ L c M post → gS L c (M ++ post) (length L + suc (length M))
                           ≡ length L + length (corIns c) + length M
gS-right []      c M post =
  trans (length-++ (corIns c) (concatIns (take (length M) (idTys (M ++ post)))))
        (cong (length (corIns c) +_)
          (trans (cong (λ xs → sumIns (take (length M) xs)) (sym (++-[] (idTys (M ++ post)))))
                 (sumIns-take-idTys M post [])))
gS-right (A ∷ L) c M post = cong suc (gS-right L c M post)

data SlotV (k g : Nat) (L : List Fm) (X : Fm) (R : List Fm) (Z : Fm) (x : V) : Set where
  left  : ∀ pre M → L ≡ pre ++ M → length pre ≡ g →
          x ∶ ((pre ++ dsrc k ++ M ++ X ∷ R) ▸ Z) → SlotV k g L X R Z x
  right : ∀ M post → R ≡ M ++ post → length L + suc (length M) ≡ g →
          x ∶ ((L ++ X ∷ M ++ dsrc k ++ post) ▸ Z) → SlotV k g L X R Z x

slot-view : ∀ {k g L X R Z x} → CellAt k g ((L ++ X ∷ R) ▸ Z) x → SlotV k g L X R Z x
slot-view {k} {g} {L} {X} {R} {Z} (cellAt pre post sp len tx) with split-mid pre post L X R sp
... | inl (M , e₁ , refl) = left pre M e₁ len tx
... | inr (M , refl , e₂) =
  right M post e₂ (trans (sym (length-++ L (X ∷ M))) len)
        (retype tx (cong (_▸ Z) (++-assoc L (X ∷ M) (dsrc k ++ post))))

module _ {L : List Fm} {c : Cor} {R : List Fm} {Z : Fm} where
  private
    X  = corOut c
    HS = (L ++ X ∷ R) ▸ Z
    BS = (L ++ corIns c ++ R) ▸ Z

  T-rS-slot : ∀ {k g x} → CellAt k g HS x → CellAt k (gS L c R g) BS (pc x (cpos L g k) (cor c))
  T-rS-slot {k} {g} {x} cx with slot-view cx
  ... | left pre M refl refl tx =
    cellAt pre (M ++ corIns c ++ R) (sym (++-assoc pre M (corIns c ++ R)))
      (sym (trans (cong (λ n → sumIns (take (length pre) n)) refl) (sumIns-take-idTys pre M _)))
      (retype (T-pc-at {P = pre ++ dsrc k ++ M} {Y = X} {Q = R}
                 (retype tx (cong (_▸ Z) (sym (++-assoc pre (dsrc k) (M ++ X ∷ R)) ⟨trans⟩
                                          sym (++-assoc (pre ++ dsrc k) M (X ∷ R)) ⟨trans⟩
                                          cong (_++ X ∷ R) (++-assoc pre (dsrc k) M))))
                 (T-cor c) pos₀)
              (cong (_▸ Z) (++-assoc pre (dsrc k ++ M) (corIns c ++ R) ⟨trans⟩
                            cong (pre ++_) (++-assoc (dsrc k) M (corIns c ++ R)))))
    where
    _⟨trans⟩_ : ∀ {A : Set} {a b d : A} → a ≡ b → b ≡ d → a ≡ d
    _⟨trans⟩_ = trans
    infixr 5 _⟨trans⟩_
    pos₀ : length (pre ++ dsrc k ++ M) ≡ cpos (pre ++ M) (length pre) k
    pos₀ = trans (length-++₃ pre (dsrc k) M)
          (trans (+-swap₂ (length pre) (length (dsrc k)) (length M))
          (trans (cong (_+ length (dsrc k)) (sym (length-++ pre M)))
                 (sym (if-T (leq (length pre) (length (pre ++ M)))
                        (subst (λ n → T (leq (length pre) n)) (sym (length-++ pre M))
                               (leq-+ (length pre) (length M)))))))
  ... | right M post refl refl tx =
    cellAt (L ++ corIns c ++ M) post
      (trans (++-assoc L (corIns c ++ M) post) (cong (L ++_) (++-assoc (corIns c) M post)))
      (trans (length-++₃ L (corIns c) M) (sym (gS-right L c M post)))
      (retype (T-pc-at {P = L} {Y = X} {Q = M ++ dsrc k ++ post} tx (T-cor c)
                 (sym (if-F (leq (length L + suc (length M)) (length L)) (leq-+suc (length L) (length M)))))
              (cong (_▸ Z) (sym (trans (++-assoc L (corIns c ++ M) (dsrc k ++ post))
                                       (cong (L ++_) (++-assoc (corIns c) M (dsrc k ++ post)))))))

  rinv-l-slot : ∀ {k g x} → CellAt k g HS x → unC c (cpos L g k) (pc x (cpos L g k) (cor c)) ≈ x
  rinv-l-slot {k} {g} {x} cx with slot-view cx
  ... | left pre M refl refl tx =
    unC-l-at {P = pre ++ dsrc k ++ M} {c = c} {Q = R}
      (retype tx (cong (_▸ Z) (trans (sym (++-assoc pre (dsrc k) (M ++ X ∷ R)))
                              (trans (sym (++-assoc (pre ++ dsrc k) M (X ∷ R)))
                                     (cong (_++ X ∷ R) (++-assoc pre (dsrc k) M))))))
      (trans (length-++₃ pre (dsrc k) M)
      (trans (+-swap₂ (length pre) (length (dsrc k)) (length M))
      (trans (cong (_+ length (dsrc k)) (sym (length-++ pre M)))
             (sym (if-T (leq (length pre) (length (pre ++ M)))
                    (subst (λ n → T (leq (length pre) n)) (sym (length-++ pre M))
                           (leq-+ (length pre) (length M))))))))
  ... | right M post refl refl tx =
    unC-l-at {P = L} {c = c} {Q = M ++ dsrc k ++ post} tx
      (sym (if-F (leq (length L + suc (length M)) (length L)) (leq-+suc (length L) (length M))))

  r-face-slot : ∀ {k g x} α → CellAt (suc k) g HS x →
    pc (pc x (cpos L g (suc k)) (cor c)) (gS L c R g) (δ α k)
      ≈ pc (pc x g (δ α k)) (cpos L g k) (cor c)
  r-face-slot {k} {g} {x} α cx with slot-view cx
  ... | left pre M refl refl tx =
    ≈-trans (≡→≈ (cong₂ (λ i j → pc (pc x i (cor c)) j (δ α k)) posA (gS-left (pre ++ M) c R (length pre) lq)))
    (≈-trans (≈-sym (par {P = pre} {Y = D (suc k)} {M = M} {W = X} {Q = R} tx (T-δ α k) (T-cor c)))
             (≡→≈ (cong (λ i → pc (pc x (length pre) (δ α k)) i (cor c)) posB)))
    where
    lq : T (leq (length pre) (length (pre ++ M)))
    lq = subst (λ n → T (leq (length pre) n)) (sym (length-++ pre M)) (leq-+ (length pre) (length M))
    posA : cpos (pre ++ M) (length pre) (suc k) ≡ length pre + suc (length M)
    posA = trans (if-T (leq (length pre) (length (pre ++ M))) lq)
           (trans (cong (_+ 1) (length-++ pre M))
           (trans (+-assoc (length pre) (length M) 1) (cong (length pre +_) (+-one (length M)))))
    posB : length pre + length (dsrc k) + length M ≡ cpos (pre ++ M) (length pre) k
    posB = trans (+-swap₂ (length pre) (length (dsrc k)) (length M))
           (trans (cong (_+ length (dsrc k)) (sym (length-++ pre M)))
                  (sym (if-T (leq (length pre) (length (pre ++ M))) lq)))
  ... | right M post refl refl tx =
    ≈-trans (≡→≈ (cong₂ (λ i j → pc (pc x i (cor c)) j (δ α k)) cq (gS-right L c M post)))
    (≈-trans (par {P = L} {Y = X} {M = M} {W = D (suc k)} {Q = post} tx (T-cor c) (T-δ α k))
             (≡→≈ (cong (λ i → pc (pc x (length L + suc (length M)) (δ α k)) i (cor c)) (sym cq′))))
    where
    cq : cpos L (length L + suc (length M)) (suc k) ≡ length L
    cq = if-F (leq (length L + suc (length M)) (length L)) (leq-+suc (length L) (length M))
    cq′ : cpos L (length L + suc (length M)) k ≡ length L
    cq′ = if-F (leq (length L + suc (length M)) (length L)) (leq-+suc (length L) (length M))

  -- reading a cell of B as a precomposite with the corolla
  record BView (k g : Nat) (y : V) : Set where
    field
      P Q  : List Fm
      ty   : y ∶ ((P ++ corIns c ++ Q) ▸ Z)
      lenP : length P ≡ cpos L g k
      cell : ∀ {u} → u ∶ ((P ++ X ∷ Q) ▸ Z) → CellAt k g HS u

  private
    reassoc₃ : ∀ (a b d e : List Fm) → (a ++ b ++ d) ++ e ≡ a ++ b ++ d ++ e
    reassoc₃ a b d e = trans (++-assoc a (b ++ d) e) (cong (a ++_) (++-assoc b d e))

    gS-right′ : ∀ m → T (leq m (length R)) → gS L c R (length L + suc m) ≡ length L + length (corIns c) + m
    gS-right′ m p =
      trans (cong (λ R′ → gS L c R′ (length L + suc m)) (sym (take-drop m R)))
      (trans (cong (λ n → gS L c (take m R ++ drop m R) (length L + suc n)) (sym (length-take m R p)))
      (trans (gS-right L c (take m R) (drop m R))
             (cong (length L + length (corIns c) +_) (length-take m R p))))

  bview : ∀ {k g y} → T (leq g (length (L ++ X ∷ R))) → CellAt k (gS L c R g) BS y → BView k g y
  bview {k} {g} {y} bd (cellAt preY postY sp len ty) with leq g (length L) in e
  ... | true = record
    { P = take g L ++ dsrc k ++ drop g L ; Q = R
    ; ty = retype ty (cong (_▸ Z) (trans (cong₂ (λ a b → a ++ dsrc k ++ b) e-pre e-post)
                                         (sym (reassoc₃ (take g L) (dsrc k) (drop g L) (corIns c ++ R)))))
    ; lenP = trans (length-++₃ (take g L) (dsrc k) (drop g L))
             (trans (cong (λ n → n + length (dsrc k) + length (drop g L)) (length-take g L lq))
             (trans (+-swap₂ g (length (dsrc k)) (length (drop g L)))
             (trans (cong (_+ length (dsrc k)) (sym lenL))
                    (sym (if-T (leq g (length L)) lq)))))
    ; cell = λ tu → cellAt (take g L) (drop g L ++ X ∷ R)
                       (trans (sym (++-assoc (take g L) (drop g L) (X ∷ R))) (cong (_++ X ∷ R) (take-drop g L)))
                       (length-take g L lq)
                       (retype tu (cong (_▸ Z) (reassoc₃ (take g L) (dsrc k) (drop g L) (X ∷ R))))
    }
    where
    lq : T (leq g (length L))
    lq = subst T (sym e) tt
    lenY : length preY ≡ g
    lenY = trans len (gS-left L c R g lq)
    su = split-unique preY postY _ sp
    e-pre : preY ≡ take g L
    e-pre = trans (fst su) (trans (cong (λ n → take n (L ++ corIns c ++ R)) lenY) (take-++ˡ g L _ lq))
    e-post : postY ≡ drop g L ++ corIns c ++ R
    e-post = trans (snd su) (trans (cong (λ n → drop n (L ++ corIns c ++ R)) lenY) (drop-++ˡ g L _ lq))
    lenL : length L ≡ g + length (drop g L)
    lenL = trans (cong length (sym (take-drop g L)))
           (trans (length-++ (take g L) (drop g L)) (cong (_+ length (drop g L)) (length-take g L lq)))
  ... | false with leq-false g (length L) e
  ...   | m , refl = record
    { P = L ; Q = take m R ++ dsrc k ++ drop m R
    ; ty = retype ty (cong (_▸ Z) (trans (cong₂ (λ a b → a ++ dsrc k ++ b) e-pre e-post)
             (trans (++-assoc L (corIns c ++ take m R) (dsrc k ++ drop m R))
                    (cong (L ++_) (++-assoc (corIns c) (take m R) (dsrc k ++ drop m R))))))
    ; lenP = sym (if-F (leq (length L + suc m) (length L)) e)
    ; cell = λ tu → cellAt (L ++ X ∷ take m R) (drop m R)
                       (trans (++-assoc L (X ∷ take m R) (drop m R)) (cong (λ r → L ++ X ∷ r) (take-drop m R)))
                       (trans (length-++ L (X ∷ take m R)) (cong (λ n → length L + suc n) (length-take m R lm)))
                       (retype tu (cong (_▸ Z) (sym (++-assoc L (X ∷ take m R) (dsrc k ++ drop m R)))))
    }
    where
    lm : T (leq m (length R))
    lm = leq-+-cancel (length L) (suc m) (suc (length R))
           (subst (λ n → T (leq (length L + suc m) n)) (length-++ L (X ∷ R)) bd)
    lenY : length preY ≡ length L + (length (corIns c) + m)
    lenY = trans len (trans (gS-right′ m lm) (+-assoc (length L) (length (corIns c)) m))
    su = split-unique preY postY _ sp
    e-pre : preY ≡ L ++ corIns c ++ take m R
    e-pre = trans (fst su) (trans (cong (λ n → take n (L ++ corIns c ++ R)) lenY)
            (trans (take-++ʳ L _ (corIns c ++ R)) (cong (L ++_) (take-++ʳ (corIns c) m R))))
    e-post : postY ≡ drop m R
    e-post = trans (snd su) (trans (cong (λ n → drop n (L ++ corIns c ++ R)) lenY)
             (trans (drop-++ʳ L _ (corIns c ++ R)) (drop-++ʳ (corIns c) m R)))

  T-rinv-slot : ∀ {k g y} → T (leq g (length (L ++ X ∷ R))) → CellAt k (gS L c R g) BS y →
                CellAt k g HS (unC c (cpos L g k) y)
  T-rinv-slot {k} {g} bd cy = BView.cell bv (T-unC-at {c = c} (BView.ty bv) (BView.lenP bv))
    where bv = bview {k} {g} bd cy

  rinv-r-slot : ∀ {k g y} → T (leq g (length (L ++ X ∷ R))) → CellAt k (gS L c R g) BS y →
                pc (unC c (cpos L g k) y) (cpos L g k) (cor c) ≈ y
  rinv-r-slot {k} {g} bd cy = unC-r-at {c = c} (BView.ty bv) (BView.lenP bv)
    where bv = bview {k} {g} bd cy

------------------------------------------------------------------------
-- All rows

rS : Row → Nat → Nat → V → V
rS (pairR L U W R Z)  g k x = pc x (cpos L g k) (cor (cm U W))
rS (probeR L Δ Θ R Z) g k x = pc x (cpos L g k) (cor (cp Δ Θ))
rS (unitR L R Z)      g k x = pc x (cpos L g k) (cor cpt)
rS (evLR Φ A C)       g k x = pc (evL A C) 1 x
rS (evRR Φ A C)       g k x = pc (evR A C) 0 x

rinvS : Row → Nat → Nat → V → V
rinvS (pairR L U W R Z)  g k y = unC (cm U W) (cpos L g k) y
rinvS (probeR L Δ Θ R Z) g k y = unC (cp Δ Θ) (cpos L g k) y
rinvS (unitR L R Z)      g k y = unC cpt (cpos L g k) y
rinvS (evLR Φ A C)       g k y = curL A C y
rinvS (evRR Φ A C)       g k y = curR A C y

rS-cong : ∀ ρ g k {x x′} → x ≈ x′ → rS ρ g k x ≈ rS ρ g k x′
rS-cong (pairR L U W R Z)  g k p = pc-cong (cpos L g k) p ≈-refl
rS-cong (probeR L Δ Θ R Z) g k p = pc-cong (cpos L g k) p ≈-refl
rS-cong (unitR L R Z)      g k p = pc-cong (cpos L g k) p ≈-refl
rS-cong (evLR Φ A C)       g k p = pc-cong 1 ≈-refl p
rS-cong (evRR Φ A C)       g k p = pc-cong 0 ≈-refl p

rinv-cong : ∀ ρ g k {y y′} → y ≈ y′ → rinvS ρ g k y ≈ rinvS ρ g k y′
rinv-cong (pairR L U W R Z)  g k p = unC-cong (cm U W) (cpos L g k) p
rinv-cong (probeR L Δ Θ R Z) g k p = unC-cong (cp Δ Θ) (cpos L g k) p
rinv-cong (unitR L R Z)      g k p = unC-cong cpt (cpos L g k) p
rinv-cong (evLR Φ A C)       g k p = curL-cong A C p
rinv-cong (evRR Φ A C)       g k p = curR-cong A C p

private
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  -- a cell of (A, Φ ▸ C) at gap 1 + g
  evL-view : ∀ {k g Φ A C y} → CellAt k (suc g) ((A ∷ Φ) ▸ C) y →
             Σ (List Fm) (λ pre → Σ (List Fm) (λ post →
               (pre ++ post ≡ Φ) × (length pre ≡ g) × (y ∶ ((A ∷ pre ++ dsrc k ++ post) ▸ C))))
  evL-view (cellAt []        post sp ()  ty)
  evL-view (cellAt (a ∷ pre) post sp len ty) with cons-inj sp
  ... | refl , sp′ = pre , post , sp′ , suc-inj len , ty

  -- a cell of (Φ, A ▸ C) at a gap g ≤ |Φ|
  evR-view : ∀ {k g Φ A C y} → T (leq g (length Φ)) → CellAt k g ((Φ ++ A ∷ []) ▸ C) y →
             Σ (List Fm) (λ pre → Σ (List Fm) (λ post →
               (pre ++ post ≡ Φ) × (length pre ≡ g) × (y ∶ (((pre ++ dsrc k ++ post) ++ A ∷ []) ▸ C))))
  evR-view {k} {g} {Φ} {A} {C} bd (cellAt pre postY sp len ty)
    with split-snoc pre postY Φ A sp (subst (λ n → T (leq n (length Φ))) (sym len) bd)
  ... | M , refl , e = pre , M , e , len ,
        retype ty (cong (_▸ C) (sym (trans (++-assoc pre (dsrc k ++ M) (A ∷ []))
                                           (cong (pre ++_) (++-assoc (dsrc k) M (A ∷ []))))))

T-rS : ∀ ρ {k g x} → CellAt k g (H ρ) x → CellAt k (rgap ρ g) (B ρ) (rS ρ g k x)
T-rS (pairR L U W R Z)  {k} {g} cx = T-rS-slot {L} {cm U W} {R} {Z} {k} {g} cx
T-rS (probeR L Δ Θ R Z) {k} {g} cx = T-rS-slot {L} {cp Δ Θ} {R} {Z} {k} {g} cx
T-rS (unitR L R Z)      {k} {g} cx = T-rS-slot {L} {cpt} {R} {Z} {k} {g} cx
T-rS (evLR Φ A C) {k} (cellAt pre post sp len tx) =
  cellAt (A ∷ pre) post (cong (A ∷_) sp) (cong suc len)
    (retype (T-pc {P = A ∷ []} {Y = A \\ C} {Q = []} (T-evL A C) tx)
            (cong (λ l → (A ∷ l) ▸ C) (++-[] (pre ++ dsrc k ++ post))))
T-rS (evRR Φ A C) {k} (cellAt pre post sp len tx) =
  cellAt pre (post ++ A ∷ []) (trans (sym (++-assoc pre post (A ∷ []))) (cong (_++ A ∷ []) sp)) len
    (retype (T-pc {P = []} {Y = C // A} {Q = A ∷ []} (T-evR A C) tx)
            (cong (_▸ C) (trans (++-assoc pre (dsrc k ++ post) (A ∷ []))
                                (cong (pre ++_) (++-assoc (dsrc k) post (A ∷ []))))))

T-rinvS : ∀ ρ {k g y} → T (leq g (length (ins (H ρ)))) → CellAt k (rgap ρ g) (B ρ) y →
          CellAt k g (H ρ) (rinvS ρ g k y)
T-rinvS (pairR L U W R Z)  {k} {g} bd cy = T-rinv-slot {L} {cm U W} {R} {Z} {k} {g} bd cy
T-rinvS (probeR L Δ Θ R Z) {k} {g} bd cy = T-rinv-slot {L} {cp Δ Θ} {R} {Z} {k} {g} bd cy
T-rinvS (unitR L R Z)      {k} {g} bd cy = T-rinv-slot {L} {cpt} {R} {Z} {k} {g} bd cy
T-rinvS (evLR Φ A C) bd cy with evL-view cy
... | pre , post , sp , len , ty = cellAt pre post sp len (T-curL ty)
T-rinvS (evRR Φ A C) bd cy with evR-view bd cy
... | pre , post , sp , len , ty = cellAt pre post sp len (T-curR ty)

rinv-l : ∀ ρ {k g x} → CellAt k g (H ρ) x → rinvS ρ g k (rS ρ g k x) ≈ x
rinv-l (pairR L U W R Z)  {k} {g} cx = rinv-l-slot {L} {cm U W} {R} {Z} {k} {g} cx
rinv-l (probeR L Δ Θ R Z) {k} {g} cx = rinv-l-slot {L} {cp Δ Θ} {R} {Z} {k} {g} cx
rinv-l (unitR L R Z)      {k} {g} cx = rinv-l-slot {L} {cpt} {R} {Z} {k} {g} cx
rinv-l (evLR Φ A C) cx = curL-l (typ cx)
rinv-l (evRR Φ A C) cx = curR-l (typ cx)

rinv-r : ∀ ρ {k g y} → T (leq g (length (ins (H ρ)))) → CellAt k (rgap ρ g) (B ρ) y →
         rS ρ g k (rinvS ρ g k y) ≈ y
rinv-r (pairR L U W R Z)  {k} {g} bd cy = rinv-r-slot {L} {cm U W} {R} {Z} {k} {g} bd cy
rinv-r (probeR L Δ Θ R Z) {k} {g} bd cy = rinv-r-slot {L} {cp Δ Θ} {R} {Z} {k} {g} bd cy
rinv-r (unitR L R Z)      {k} {g} bd cy = rinv-r-slot {L} {cpt} {R} {Z} {k} {g} bd cy
rinv-r (evLR Φ A C) bd cy with evL-view cy
... | pre , post , sp , len , ty = curL-r ty
rinv-r (evRR Φ A C) bd cy with evR-view bd cy
... | pre , post , sp , len , ty = curR-r ty

r-face : ∀ ρ {k g x} α → CellAt (suc k) g (H ρ) x →
         pc (rS ρ g (suc k) x) (rgap ρ g) (δ α k) ≈ rS ρ g k (pc x g (δ α k))
r-face (pairR L U W R Z)  {k} {g} α cx = r-face-slot {L} {cm U W} {R} {Z} {k} {g} α cx
r-face (probeR L Δ Θ R Z) {k} {g} α cx = r-face-slot {L} {cp Δ Θ} {R} {Z} {k} {g} α cx
r-face (unitR L R Z)      {k} {g} α cx = r-face-slot {L} {cpt} {R} {Z} {k} {g} α cx
r-face (evLR Φ A C) {k} α (cellAt pre post sp refl tx) =
  seq {P = A ∷ []} {Y = A \\ C} {Q = []} {P′ = pre} (T-evL A C) tx (T-δ α k)
r-face (evRR Φ A C) {k} α (cellAt pre post sp refl tx) =
  seq {P = []} {Y = C // A} {Q = A ∷ []} {P′ = pre} (T-evR A C) tx (T-δ α k)

rinv-face : ∀ ρ {k g y} α → T (leq g (length (ins (H ρ)))) → CellAt (suc k) (rgap ρ g) (B ρ) y →
            pc (rinvS ρ g (suc k) y) g (δ α k) ≈ rinvS ρ g k (pc y (rgap ρ g) (δ α k))
rinv-face ρ {k} {g} {y} α bd cy =
  ≈-trans (≈-sym (rinv-l ρ (face-cell α cx)))
  (rinv-cong ρ g k (≈-trans (≈-sym (r-face ρ α cx))
                            (pc-cong (rgap ρ g) (rinv-r ρ bd cy) ≈-refl)))
  where cx = T-rinvS ρ bd cy
