------------------------------------------------------------------------
-- Theorem S, generic part: soundness of the coherence terms
-- here t gc φs ts (the cell c, the inverse image of the ball b under r)
-- and here t gε φs ts (the flat cell from r(c) to the collared b).
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.SemHere (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.ListLemmas
open import Agda.Builtin.Nat using (_*_)
open Model 𝔐
open import CaTTExp.Gray.Biclosed.ModelFacts 𝔐
open import CaTTExp.Gray.Biclosed.RowSem 𝔐
open import CaTTExp.Gray.Biclosed.Sem 𝔐
open import CaTTExp.Gray.Biclosed.SemComp 𝔐

------------------------------------------------------------------------
-- Substitution and the rows

sFs-++ : ∀ φ xs ys → sFs φ (xs ++ ys) ≡ sFs φ xs ++ sFs φ ys
sFs-++ φ []       ys = refl
sFs-++ φ (x ∷ xs) ys = cong (sF φ x ∷_) (sFs-++ φ xs ys)

length-sFs : ∀ φ xs → length (sFs φ xs) ≡ length xs
length-sFs φ []       = refl
length-sFs φ (x ∷ xs) = cong suc (length-sFs φ xs)

sM-H : ∀ φ ρ → sM φ (H ρ) ≡ H (sRow φ ρ)
sM-H φ (pairR L U W R Z)  = cong (_▸ sF φ Z) (sFs-++ φ L ((U ⊗ W) ∷ R))
sM-H φ (probeR L Δ Θ R Z) = cong (_▸ sF φ Z) (sFs-++ φ L (rep (Δ ⊠ Θ) ∷ R))
sM-H φ (unitR L R Z)      = cong (_▸ sF φ Z) (sFs-++ φ L (rep (disk 0) ∷ R))
sM-H φ (evLR Φ A C)       = refl
sM-H φ (evRR Φ A C)       = refl

sM-B : ∀ φ ρ → sM φ (B ρ) ≡ B (sRow φ ρ)
sM-B φ (pairR L U W R Z)  = cong (_▸ sF φ Z) (sFs-++ φ L (U ∷ W ∷ R))
sM-B φ (probeR L Δ Θ R Z) = cong (_▸ sF φ Z) (sFs-++ φ L (rep Δ ∷ rep Θ ∷ R))
sM-B φ (unitR L R Z)      = cong (_▸ sF φ Z) (sFs-++ φ L R)
sM-B φ (evLR Φ A C)       = refl
sM-B φ (evRR Φ A C)       = cong (_▸ sF φ C) (sFs-++ φ Φ (A ∷ []))

sTs-++ : ∀ σ xs ys → sTs σ (xs ++ ys) ≡ sTs σ xs ++ sTs σ ys
sTs-++ σ []       ys = refl
sTs-++ σ (x ∷ xs) ys = cong (sT σ x ∷_) (sTs-++ σ xs ys)

sTs-ids : ∀ σ L → sTs σ (ids L) ≡ ids (sFs (fo σ) L)
sTs-ids σ []      = refl
sTs-ids σ (A ∷ L) = cong (idt (sF (fo σ) A) ∷_) (sTs-ids σ L)

sTs-slot : ∀ σ L y R → sTs σ (ids L ++ y ∷ ids R) ≡ ids (sFs (fo σ) L) ++ sT σ y ∷ ids (sFs (fo σ) R)
sTs-slot σ L y R = trans (sTs-++ σ (ids L) (y ∷ ids R))
                         (cong₂ (λ a b → a ++ sT σ y ∷ b) (sTs-ids σ L) (sTs-ids σ R))

sT-rmap : ∀ σ ρ x → sT σ (rmap ρ x) ≡ rmap (sRow (fo σ) ρ) (sT σ x)
sT-rmap σ (pairR L U W R Z)  x = cong (comp (sT σ x)) (sTs-slot σ L (mP U W) R)
sT-rmap σ (probeR L Δ Θ R Z) x = cong (comp (sT σ x)) (sTs-slot σ L (pP Δ Θ) R)
sT-rmap σ (unitR L R Z)      x = cong (comp (sT σ x)) (sTs-slot σ L pt R)
sT-rmap σ (evLR Φ A C)       x = refl
sT-rmap σ (evRR Φ A C)       x = refl

-- the gap of r does not see the formulas
idTys-sFs : ∀ φ L → idTys (sFs φ L) ≡ map (sM φ) (idTys L)
idTys-sFs φ []      = refl
idTys-sFs φ (A ∷ L) = cong (_ ∷_) (idTys-sFs φ L)

sumIns-sM : ∀ φ ms → sumIns (map (sM φ) ms) ≡ sumIns ms
sumIns-sM φ []       = refl
sumIns-sM φ (M ∷ ms) =
  trans (length-++ (sFs φ (ins M)) (concatIns (map (sM φ) ms)))
  (trans (cong₂ _+_ (length-sFs φ (ins M)) (sumIns-sM φ ms)) (sym (length-++ (ins M) (concatIns ms))))

slot-gap : ∀ φ L C R g → sumIns (take g (idTys (sFs φ L) ++ sM φ C ∷ idTys (sFs φ R)))
                          ≡ sumIns (take g (idTys L ++ C ∷ idTys R))
slot-gap φ L C R g =
  trans (cong (λ l → sumIns (take g l))
          (trans (cong₂ (λ a b → a ++ sM φ C ∷ b) (idTys-sFs φ L) (idTys-sFs φ R))
                 (sym (map-++ (sM φ) (idTys L) (C ∷ idTys R)))))
  (trans (cong sumIns (take-map (sM φ) g (idTys L ++ C ∷ idTys R)))
         (sumIns-sM φ (take g (idTys L ++ C ∷ idTys R))))

rgap-sRow : ∀ φ ρ g → rgap (sRow φ ρ) g ≡ rgap ρ g
rgap-sRow φ (pairR L U W R Z)  g = slot-gap φ L ((U ∷ W ∷ []) ▸ (U ⊗ W)) R g
rgap-sRow φ (probeR L Δ Θ R Z) g = slot-gap φ L ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) R g
rgap-sRow φ (unitR L R Z)      g = slot-gap φ L ([] ▸ rep (disk 0)) R g
rgap-sRow φ (evLR Φ A C)       g = refl
rgap-sRow φ (evRR Φ A C)       g = refl

-- r maps gaps of H to gaps of B
sumIns-take-≤ : ∀ g ms → T (leq (sumIns (take g ms)) (sumIns ms))
sumIns-take-≤ g ms =
  subst (λ n → T (leq (sumIns (take g ms)) n))
        (trans (sym (sumIns-++ (take g ms) (drop g ms))) (cong sumIns (take-drop g ms)))
        (leq-+ (sumIns (take g ms)) (sumIns (drop g ms)))

leq-suc′ : ∀ a b → T (leq a b) → T (leq a (suc b))
leq-suc′ zero    b       p = tt
leq-suc′ (suc a) (suc b) p = leq-suc′ a b p

slot-total : ∀ L C R → sumIns (idTys L ++ C ∷ idTys R) ≡ length (L ++ ins C ++ R)
slot-total L C R =
  trans (sumIns-++ (idTys L) (C ∷ idTys R))
  (trans (cong₂ _+_ (cong length (concatIns-idTys L))
                    (trans (length-++ (ins C) (concatIns (idTys R)))
                           (trans (cong (length (ins C) +_) (cong length (concatIns-idTys R)))
                                  (sym (length-++ (ins C) R)))))
         (sym (length-++ L (ins C ++ R))))

rgap-bound : ∀ ρ g → T (leq g (length (ins (H ρ)))) → T (leq (rgap ρ g) (length (ins (B ρ))))
rgap-bound (pairR L U W R Z)  g _ =
  subst (λ n → T (leq (sumIns (take g (idTys L ++ ((U ∷ W ∷ []) ▸ (U ⊗ W)) ∷ idTys R))) n)) (slot-total L ((U ∷ W ∷ []) ▸ (U ⊗ W)) R)
        (sumIns-take-≤ g (idTys L ++ ((U ∷ W ∷ []) ▸ (U ⊗ W)) ∷ idTys R))
rgap-bound (probeR L Δ Θ R Z) g _ =
  subst (λ n → T (leq (sumIns (take g (idTys L ++ ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) ∷ idTys R))) n)) (slot-total L ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) R)
        (sumIns-take-≤ g (idTys L ++ ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) ∷ idTys R))
rgap-bound (unitR L R Z)      g _ =
  subst (λ n → T (leq (sumIns (take g (idTys L ++ ([] ▸ rep (disk 0)) ∷ idTys R))) n)) (slot-total L ([] ▸ rep (disk 0)) R)
        (sumIns-take-≤ g (idTys L ++ ([] ▸ rep (disk 0)) ∷ idTys R))
rgap-bound (evLR Φ A C)       g p = p
rgap-bound (evRR Φ A C)       g p =
  subst (λ n → T (leq g n)) (sym (trans (length-++ Φ (A ∷ [])) (+-comm (length Φ) 1)))
        (leq-suc′ g (length Φ) p)

H-bound : ∀ φ ρ g → T (leq g (length (ins (H ρ)))) → T (leq g (length (ins (H (sRow φ ρ)))))
H-bound φ ρ g p = subst (λ n → T (leq g n))
  (trans (sym (length-sFs φ (ins (H ρ)))) (cong (λ M → length (ins M)) (sM-H φ ρ))) p

------------------------------------------------------------------------
-- The generic types of a template

module _ (σ : Sub) (t : Tmpl) where
  dim-tyU : ∀ j → dim (sY σ (tyU t j)) ≡ j
  dim-tyU zero    = refl
  dim-tyU (suc j) = cong suc (dim-tyU j)

  dim-tyB : ∀ j → dim (sY σ (tyB t j)) ≡ j
  dim-tyB zero    = refl
  dim-tyB (suc j) = cong suc (dim-tyB j)

  dim-tyRU : ∀ j → dim (sY σ (tyRU t j)) ≡ j
  dim-tyRU zero    = refl
  dim-tyRU (suc j) = cong suc (dim-tyRU j)

  base-tyU : ∀ j → baseM (sY σ (tyU t j)) ≡ sM (fo σ) (H (row t))
  base-tyU zero    = refl
  base-tyU (suc j) = base-tyU j

  base-tyB : ∀ j → baseM (sY σ (tyB t j)) ≡ sM (fo σ) (B (row t))
  base-tyB zero    = refl
  base-tyB (suc j) = base-tyB j

  base-tyRU : ∀ j → baseM (sY σ (tyRU t j)) ≡ sM (fo σ) (B (row t))
  base-tyRU zero    = refl
  base-tyRU (suc j) = base-tyRU j

  gap-tyU : ∀ j → gapIs (gap t) (sY σ (tyU t j))
  gap-tyU zero    = tt
  gap-tyU (suc j) = refl

  gap-tyB : ∀ j → gapIs (rgap (row t) (gap t)) (sY σ (tyB t j))
  gap-tyB zero    = tt
  gap-tyB (suc j) = refl

  gap-tyRU : ∀ j → gapIs (rgap (row t) (gap t)) (sY σ (tyRU t j))
  gap-tyRU zero    = tt
  gap-tyRU (suc j) = refl

  length-levels′ : ∀ j → length (levels t j) ≡ j * 6
  length-levels′ zero    = refl
  length-levels′ (suc j) =
    trans (length-++ (levels t j) (block t j)) (trans (cong (_+ 6) (length-levels′ j)) (+-comm (j * 6) 6))

  -- entries of the top block and the ball
  lookup-top : ∀ m o rest → lookup ((levels t m ++ block t m) ++ rest) (o + m * 6) ≡ lookup (block t m ++ rest) o
  lookup-top m o rest =
    trans (cong (λ l → lookup l (o + m * 6)) (++-assoc (levels t m) (block t m) rest))
    (trans (cong (lookup (levels t m ++ block t m ++ rest))
                 (trans (+-comm o (m * 6)) (cong (_+ o) (sym (length-levels′ m)))))
           (lookup-++ʳ (levels t m) (block t m ++ rest) o))
    where
    lookup-++ʳ : ∀ {A : Set} (xs ys : List A) i → lookup (xs ++ ys) (length xs + i) ≡ lookup ys i
    lookup-++ʳ []       ys i = refl
    lookup-++ʳ (x ∷ xs) ys i = lookup-++ʳ xs ys i

  lookup-ball : ∀ n → lookup (levels t n ++ tyB t n ∷ []) (0 + n * 6) ≡ just (tyB t n)
  lookup-ball n = trans (cong (lookup (levels t n ++ tyB t n ∷ []))
                              (trans (sym (+-zero (n * 6))) (cong (_+ 0) (sym (length-levels′ n)))))
                        (go (levels t n))
    where
    go : ∀ xs → lookup (xs ++ tyB t n ∷ []) (length xs + 0) ≡ just (tyB t n)
    go []       = refl
    go (x ∷ xs) = go xs

------------------------------------------------------------------------
-- The identity instance, substituted

objs-inst : ∀ φs → sFs (nthF φs) (objsFrom 0 (length φs)) ≡ φs
objs-inst φs = go [] φs
  where
  shift : ∀ x xs a n → sFs (nthF (x ∷ xs)) (objsFrom (suc a) n) ≡ sFs (nthF xs) (objsFrom a n)
  shift x xs a zero    = refl
  shift x xs a (suc n) = cong (nthF xs a ∷_) (shift x xs (suc a) n)
  go : ∀ (pre xs : List Fm) → sFs (nthF xs) (objsFrom 0 (length xs)) ≡ xs
  go pre []       = refl
  go pre (x ∷ xs) = cong (x ∷_) (trans (shift x xs 0 (length xs)) (go pre xs))

vars-inst : ∀ φs ts → sTs (instS φs ts) (varsFrom 0 (length ts)) ≡ ts
vars-inst φs ts = go ts
  where
  shift : ∀ x xs a n → sTs (instS φs (x ∷ xs)) (varsFrom (suc a) n) ≡ sTs (instS φs xs) (varsFrom a n)
  shift x xs a zero    = refl
  shift x xs a (suc n) = cong (nthT xs a ∷_) (shift x xs (suc a) n)
  go : ∀ xs → sTs (instS φs xs) (varsFrom 0 (length xs)) ≡ xs
  go []       = refl
  go (x ∷ xs) = cong (x ∷_) (trans (shift x xs 0 (length xs)) (go xs))

sT-cterm : ∀ t φs ts → length φs ≡ nObj t → length ts ≡ nCtx t →
           sT (instS φs ts) (cterm t) ≡ here t gc φs ts
sT-cterm t φs ts lφ lts =
  cong₂ (here t gc)
    (trans (cong (λ k → sFs (nthF φs) (objsFrom 0 k)) (sym lφ)) (objs-inst φs))
    (trans (cong (λ k → sTs (instS φs ts) (varsFrom 0 k)) (sym lts)) (vars-inst φs ts))

------------------------------------------------------------------------
-- Composing with identities and one corolla

length-map-idv : ∀ M → length (map idv M) ≡ length M
length-map-idv M = length-map idv M

cmp-ids-cor : ∀ {F P M c R Q Z i} → F ∶ ((P ++ M ++ corOut c ∷ R ++ Q) ▸ Z) → length P ≡ i →
              cmpFrom F i (map idv M ++ cor c ∷ map idv R) ≈ pc F (i + length M) (cor c)
cmp-ids-cor {F} {P} {M} {c} {R} {Q} {Z} {i} pF refl =
  ≈-trans (≡→≈ (cmpFrom-++ F i (map idv M) (cor c ∷ map idv R)))
  (≈-trans (cmpFrom-cong i (map idv M) (≈-trans (pc-cong j inner ≈-refl) (≡→≈ (cong (λ k → pc F k (cor c)) ej))))
           (cmp-ids {P = P} {L = M} {Q = corIns c ++ R ++ Q} (∶-≈ ≈-refl tpc) refl))
  where
  j = i + length (map idv M)
  ej : j ≡ i + length M
  ej = cong (i +_) (length-map-idv M)
  inner : cmpFrom F (suc j) (map idv R) ≈ F
  inner = cmp-ids {P = P ++ M ++ corOut c ∷ []} {L = R} {Q = Q}
            (retype pF (cong (_▸ Z) (trans (cong (P ++_) (snoc-hinge M (corOut c) (R ++ Q)))
                                           (sym (++-assoc P (M ++ corOut c ∷ []) (R ++ Q))))))
            (trans (length-++ P (M ++ corOut c ∷ []))
            (trans (cong (i +_) (length-snoc M (corOut c)))
            (trans (+-suc i (length M)) (cong suc (sym ej)))))
  tpc : pc F (i + length M) (cor c) ∶ ((P ++ M ++ corIns c ++ R ++ Q) ▸ Z)
  tpc = retype (T-pc-at {P = P ++ M} {Y = corOut c} {Q = R ++ Q}
                  (retype pF (cong (_▸ Z) (sym (++-assoc P M (corOut c ∷ R ++ Q))))) (T-cor c)
                  (length-++ P M))
               (cong (_▸ Z) (++-assoc P M (corIns c ++ R ++ Q)))

cpos-0 : ∀ L g → cpos L g 0 ≡ length L
cpos-0 L g with leq g (length L)
... | true  = +-zero (length L)
... | false = refl

drop-split : ∀ {A : Set} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
drop-split []       ys = refl
drop-split (x ∷ xs) ys = drop-split xs ys

------------------------------------------------------------------------
-- The interpretation of r(x)

gpOK : Nat → Nat → SC → Set
gpOK zero    g x = ⊤
gpOK (suc k) g x = gp x ≡ g

-- a cell of H at gap g, as a semantic cell
record RD (ρ : Row) (k g : Nat) (x : SC) : Set where
  field
    rcell : CellAt k g (H ρ) (val x)
    rar   : ar x ≡ length (ins (H ρ))
    rdm   : dm x ≡ k
    rgp   : gpOK k g x
open RD public

-- r(x) as a semantic cell
record RO (ρ : Row) (k g : Nat) (x y : SC) : Set where
  field
    oval : val y ≈ rS ρ g k (val x)
    oar  : ar y ≡ length (ins (B ρ))
    odm  : dm y ≡ k
    ogp  : gpOK k (rgap ρ g) y
open RO public

ArM : List MTy → List SC → Set
ArM = All2 (λ M c → ar c ≡ length (ins M))

sumAr-ArM : ∀ {ms cs} → ArM ms cs → sumAr cs ≡ sumIns ms
sumAr-ArM []                = refl
sumAr-ArM {M ∷ ms} (a ∷ as) = trans (cong₂ _+_ a (sumAr-ArM as)) (sym (length-++ (ins M) (concatIns ms)))

ArM-ids : ∀ L → ArM (idTys L) (map idSC L)
ArM-ids []      = []
ArM-ids (A ∷ L) = refl ∷ ArM-ids L

vals-ids : ∀ L → vals (map idSC L) ≡ map idv L
vals-ids []      = refl
vals-ids (A ∷ L) = cong (idv A ∷_) (vals-ids L)

hiD-ids : ∀ L cs → hiD (map idSC L ++ cs) ≡ hiD cs
hiD-ids []      cs = refl
hiD-ids (A ∷ L) cs = hiD-ids L cs

hiG-ids : ∀ L cs → hiG (map idSC L ++ cs) ≡ length L + hiG cs
hiG-ids []      cs = refl
hiG-ids (A ∷ L) cs = cong suc (hiG-ids L cs)

hiD-1 : ∀ x k → dm x ≡ k → hiD (x ∷ []) ≡ k
hiD-1 (sc v a zero g)    .zero    refl = refl
hiD-1 (sc v a (suc k) g) .(suc k) refl = refl

module _ {L : List Fm} {c : Cor} {R : List Fm} {Z : Fm} where
  private
    X  = corOut c
    cs = map idSC L ++ corSC c ∷ map idSC R
    ms = idTys L ++ (corIns c ▸ corOut c) ∷ idTys R

  slot-arM : ArM ms cs
  slot-arM = All2-++ (ArM-ids L) (refl ∷ ArM-ids R)

  slot-vals : vals cs ≡ map idv L ++ cor c ∷ map idv R
  slot-vals = trans (map-++ val (map idSC L) (corSC c ∷ map idSC R))
                    (cong₂ (λ a b → a ++ cor c ∷ b) (vals-ids L) (vals-ids R))

  slotSem : ∀ {k g} x → CellAt k g ((L ++ X ∷ R) ▸ Z) (val x) → dm x ≡ k → gpOK k g x →
            (val (compS x cs) ≈ pc (val x) (cpos L g k) (cor c)) ×
            (ar (compS x cs) ≡ length (L ++ corIns c ++ R)) × (dm (compS x cs) ≡ k) ×
            gpOK k (gS L c R g) (compS x cs)
  slotSem {zero} {g} x (cellAt pre post sp len tx) d =
    λ _ → subst (λ y → (val y ≈ pc (val x) (cpos L g 0) (cor c)) × (ar y ≡ length (L ++ corIns c ++ R)) ×
                       (dm y ≡ 0) × ⊤)
                (sym (compS-0 x cs d))
          ( ≈-trans (≡→≈ (cong (cmpFrom (val x) 0) slot-vals))
            (≈-trans (cmp-ids-cor {P = []} {M = L} {c = c} {R = R} {Q = []}
                        (retype tx (cong (_▸ Z) (trans sp (cong (L ++_) (cong (X ∷_) (sym (++-[] R))))))) refl)
                     (≡→≈ (cong (λ i → pc (val x) i (cor c)) (sym (cpos-0 L g)))))
          , trans (sumAr-ArM slot-arM) (slot-total L (corIns c ▸ corOut c) R)
          , trans (hiD-ids L (corSC c ∷ map idSC R)) (trans (cong hiD (sym (++-[] (map idSC R)))) (hiD-ids R []))
          , tt )
  slotSem {suc d} {g} x cx dx gx with slot-view cx
  ... | left pre M refl refl tx =
    subst (λ y → (val y ≈ pc (val x) (cpos (pre ++ M) (length pre) (suc d)) (cor c)) ×
                 (ar y ≡ length ((pre ++ M) ++ corIns c ++ R)) × (dm y ≡ suc d) ×
                 (gp y ≡ gS (pre ++ M) c R (length pre)))
          (sym (trans (compS-suc x cs₀ d dx) (cong (λ h → sc (whS (suc d) (val x) (vals (take h cs₀)) (vals (drop h cs₀))) (sumAr cs₀) (suc d) (sumAr (take h cs₀))) gx)))
          ( ≈-trans (≡→≈ (cong₂ (whS (suc d) (val x)) (cong vals e-take) (cong vals e-drop)))
            (≈-trans (≡→≈ (cong₂ (whS (suc d) (val x)) (vals-ids pre)
                              (trans (map-++ val (map idSC M) (corSC c ∷ map idSC R))
                                     (cong₂ (λ a b → a ++ cor c ∷ b) (vals-ids M) (vals-ids R)))))
            (≈-trans (cmpFrom-cong 0 (map idv pre) inner)
            (≈-trans (cmp-ids {P = []} {L = pre} {Q = D (suc d) ∷ M ++ corIns c ++ R} tpc refl)
                     (≡→≈ (cong (λ i → pc (val x) i (cor c)) epos)))))
          , trans (sumAr-ArM slot-arM) (slot-total (pre ++ M) (corIns c ▸ corOut c) R)
          , refl
          , sumAr-take )
    where
    cs₀ = map idSC (pre ++ M) ++ corSC c ∷ map idSC R
    e-cs : cs₀ ≡ map idSC pre ++ map idSC M ++ corSC c ∷ map idSC R
    e-cs = trans (cong (_++ corSC c ∷ map idSC R) (map-++ idSC pre M))
                 (++-assoc (map idSC pre) (map idSC M) (corSC c ∷ map idSC R))
    lp : length (map idSC pre) ≡ length pre
    lp = length-map idSC pre
    e-take : take (length pre) cs₀ ≡ map idSC pre
    e-take = trans (cong (take (length pre)) e-cs)
             (trans (cong (λ n → take n (map idSC pre ++ _)) (sym lp)) (take-split (map idSC pre) _))
    e-drop : drop (length pre) cs₀ ≡ map idSC M ++ corSC c ∷ map idSC R
    e-drop = trans (cong (drop (length pre)) e-cs)
             (trans (cong (λ n → drop n (map idSC pre ++ _)) (sym lp)) (drop-split (map idSC pre) _))
    i₀ = length (map idv pre) + 1
    inner : cmpFrom (val x) i₀ (map idv M ++ cor c ∷ map idv R) ≈ pc (val x) (i₀ + length M) (cor c)
    inner = cmp-ids-cor {P = pre ++ D (suc d) ∷ []} {M = M} {c = c} {R = R} {Q = []}
              (retype tx (cong (_▸ Z) (trans (snoc-hinge pre (D (suc d)) (M ++ X ∷ R))
                                             (cong (λ l → (pre ++ D (suc d) ∷ []) ++ M ++ X ∷ l) (sym (++-[] R))))))
              (trans (length-snoc pre (D (suc d)))
                     (trans (cong suc (sym (length-map idv pre))) (sym (+-one (length (map idv pre))))))
    tpc : pc (val x) (i₀ + length M) (cor c) ∶ (([] ++ pre ++ D (suc d) ∷ M ++ corIns c ++ R) ▸ Z)
    tpc = retype (T-pc-at {P = pre ++ D (suc d) ∷ M} {Y = X} {Q = R}
                    (retype tx (cong (_▸ Z) (sym (++-assoc pre (D (suc d) ∷ M) (X ∷ R))))) (T-cor c)
                    (trans (length-++ pre (D (suc d) ∷ M))
                    (trans (+-suc (length pre) (length M))
                    (trans (cong suc (cong (_+ length M) (sym (length-map idv pre))))
                           (cong (_+ length M) (sym (+-one (length (map idv pre)))))))))
                 (cong (_▸ Z) (++-assoc pre (D (suc d) ∷ M) (corIns c ++ R)))
    lq : T (leq (length pre) (length (pre ++ M)))
    lq = subst (λ n → T (leq (length pre) n)) (sym (length-++ pre M)) (leq-+ (length pre) (length M))
    epos : i₀ + length M ≡ cpos (pre ++ M) (length pre) (suc d)
    epos = trans (cong (λ n → n + 1 + length M) (length-map idv pre))
           (trans (+-swap₂ (length pre) 1 (length M))
           (trans (cong (_+ 1) (sym (length-++ pre M)))
                  (sym (if-T (leq (length pre) (length (pre ++ M))) lq))))
    sumAr-take : sumAr (take (length pre) cs₀) ≡ gS (pre ++ M) c R (length pre)
    sumAr-take = sumAr-ArM (All2-take (length pre) slot-arM)
  ... | right M post refl refl tx =
    subst (λ y → (val y ≈ pc (val x) (cpos L g′ (suc d)) (cor c)) ×
                 (ar y ≡ length (L ++ corIns c ++ M ++ post)) × (dm y ≡ suc d) ×
                 (gp y ≡ gS L c (M ++ post) g′))
          (sym (trans (compS-suc x cs₀ d dx) (cong (λ h → sc (whS (suc d) (val x) (vals (take h cs₀)) (vals (drop h cs₀))) (sumAr cs₀) (suc d) (sumAr (take h cs₀))) gx)))
          ( ≈-trans (≡→≈ (cong₂ (whS (suc d) (val x)) (cong vals e-take) (cong vals e-drop)))
            (≈-trans (≡→≈ (cong₂ (whS (suc d) (val x)) first-vals (vals-ids post)))
            (≈-trans (cmpFrom-cong 0 (map idv L ++ cor c ∷ map idv M) inner)
            (≈-trans (cmp-ids-cor {P = []} {M = L} {c = c} {R = M} {Q = D (suc d) ∷ post} tx refl)
                     (≡→≈ (cong (λ i → pc (val x) i (cor c)) (sym cq))))))
          , trans (sumAr-ArM slot-arM) (slot-total L (corIns c ▸ corOut c) (M ++ post))
          , refl
          , sumAr-ArM (All2-take g′ slot-arM) )
    where
    g′ = length L + suc (length M)
    first = map idSC L ++ corSC c ∷ map idSC M
    cs₀ = map idSC L ++ corSC c ∷ map idSC (M ++ post)
    e-cs : cs₀ ≡ first ++ map idSC post
    e-cs = trans (cong (λ l → map idSC L ++ corSC c ∷ l) (map-++ idSC M post))
                 (sym (++-assoc (map idSC L) (corSC c ∷ map idSC M) (map idSC post)))
    lf : length first ≡ g′
    lf = trans (length-++ (map idSC L) (corSC c ∷ map idSC M))
               (cong₂ (λ a b → a + suc b) (length-map idSC L) (length-map idSC M))
    e-take : take g′ cs₀ ≡ first
    e-take = trans (cong (take g′) e-cs) (trans (cong (λ n → take n (first ++ map idSC post)) (sym lf)) (take-split first _))
    e-drop : drop g′ cs₀ ≡ map idSC post
    e-drop = trans (cong (drop g′) e-cs) (trans (cong (λ n → drop n (first ++ map idSC post)) (sym lf)) (drop-split first _))
    first-vals : vals first ≡ map idv L ++ cor c ∷ map idv M
    first-vals = trans (map-++ val (map idSC L) (corSC c ∷ map idSC M))
                       (cong₂ (λ a b → a ++ cor c ∷ b) (vals-ids L) (vals-ids M))
    inner : cmpFrom (val x) (length (map idv L ++ cor c ∷ map idv M) + 1) (map idv post) ≈ val x
    inner = cmp-ids {P = L ++ X ∷ M ++ D (suc d) ∷ []} {L = post} {Q = []}
              (retype tx (cong (_▸ Z) (trans (cong (λ l → L ++ X ∷ l) (snoc-hinge M (D (suc d)) post))
                    (trans (sym (++-assoc L (X ∷ M ++ D (suc d) ∷ []) post))
                           (cong ((L ++ X ∷ M ++ D (suc d) ∷ []) ++_) (sym (++-[] post)))))))
              (trans (length-++ L (X ∷ M ++ D (suc d) ∷ []))
              (trans (cong (λ n → length L + suc n) (length-snoc M (D (suc d))))
              (trans (+-suc (length L) (suc (length M)))
              (trans (cong suc (sym lf′)) (sym (+-one (length (map idv L ++ cor c ∷ map idv M))))))))
      where
      lf′ : length (map idv L ++ cor c ∷ map idv M) ≡ g′
      lf′ = trans (length-++ (map idv L) (cor c ∷ map idv M))
                  (cong₂ (λ a b → a + suc b) (length-map idv L) (length-map idv M))
    cq : cpos L g′ (suc d) ≡ 0 + length L
    cq = if-F (leq (length L + suc (length M)) (length L)) (leq-+suc (length L) (length M))

------------------------------------------------------------------------
-- Building and reading memberships of hom types up to equations

mkHom : ∀ {m g A MA s t c} k M → dim A ≡ k → baseM A ≡ M → CellAt (suc k) g M (val c) →
        ar c ≡ length (ins M) → dm c ≡ suc k → gp c ≡ g → gapIs g A → MA s → MA t →
        pc (val c) g (δ false k) ≈ val s → pc (val c) g (δ true k) ≈ val t →
        (m ≡ inv → val s ≈ val t) → HomMem m g A MA s t c
mkHom k M refl refl ce a d gq ga ms mt fs ft fl =
  record { cell = ce ; mAr = a ; mDm = d ; mGp = gq ; gapA = ga ; memS = ms ; memT = mt
         ; fS = fs ; fT = ft ; flat = fl }

cell′ : ∀ {m g A MA s t c} k M → dim A ≡ k → baseM A ≡ M → HomMem m g A MA s t c → CellAt (suc k) g M (val c)
cell′ k M refl refl h = cell h

fS′ : ∀ {m g A MA s t c} k → dim A ≡ k → HomMem m g A MA s t c → pc (val c) g (δ false k) ≈ val s
fS′ k refl h = fS h

fT′ : ∀ {m g A MA s t c} k → dim A ≡ k → HomMem m g A MA s t c → pc (val c) g (δ true k) ≈ val t
fT′ k refl h = fT h

cell-gap : ∀ {k g g′ M x} → g ≡ g′ → CellAt k g M x → CellAt k g′ M x
cell-gap refl c = c

okT-bound : ∀ ρ g md n → T (okT (tmpl ρ g md n)) → T (leq g (length (ins (H ρ))))
okT-bound ρ g md zero ok =
  subst (λ h → T (leq h (length (ins (H ρ)))))
        (sym (==ℕ-sound g _ (∧-snd {eqMode md inv} (∧-snd {canon ρ} ok))))
        (leq-refl′ (length (ins (H ρ))))
  where
  leq-refl′ : ∀ n → T (leq n n)
  leq-refl′ zero    = tt
  leq-refl′ (suc n) = leq-refl′ n
okT-bound ρ g md (suc n) ok = ∧-snd {canon ρ} ok

lookupAll2 : ∀ {R : Tm → CTy → Set} {ts Δ} → All2 R ts Δ → ∀ i {A} → lookup Δ i ≡ just A → R (nthT ts i) A
lookupAll2 []       i       ()
lookupAll2 (p ∷ ps) zero    refl = p
lookupAll2 (p ∷ ps) (suc i) e    = lookupAll2 ps i e

------------------------------------------------------------------------
-- Semantic facts about r and the template

module _ (ε : Nat → SC) where
  open Interp ε

  ⟦++⟧ : ∀ xs ys → ⟦ xs ++ ys ⟧s ≡ ⟦ xs ⟧s ++ ⟦ ys ⟧s
  ⟦++⟧ []       ys = refl
  ⟦++⟧ (x ∷ xs) ys = cong (⟦ x ⟧ ∷_) (⟦++⟧ xs ys)

  ⟦ids⟧ : ∀ L → ⟦ ids L ⟧s ≡ map idSC L
  ⟦ids⟧ []      = refl
  ⟦ids⟧ (A ∷ L) = cong (idSC A ∷_) (⟦ids⟧ L)

  ⟦slot⟧ : ∀ L y R → ⟦ ids L ++ y ∷ ids R ⟧s ≡ map idSC L ++ ⟦ y ⟧ ∷ map idSC R
  ⟦slot⟧ L y R = trans (⟦++⟧ (ids L) (y ∷ ids R)) (cong₂ (λ a b → a ++ ⟦ y ⟧ ∷ b) (⟦ids⟧ L) (⟦ids⟧ R))

  ⟦nthT⟧ : ∀ ts i → ⟦ nthT ts i ⟧ ≡ nthS ⟦ ts ⟧s i
  ⟦nthT⟧ []       i       = refl
  ⟦nthT⟧ (x ∷ xs) zero    = refl
  ⟦nthT⟧ (x ∷ xs) (suc i) = ⟦nthT⟧ xs i

  ⟦chain⟧ : ∀ σ t j y → ⟦ sT σ (chain t j y) ⟧ ≡ ⟦ sT σ y ⟧
  ⟦chain⟧ σ t zero    y = refl
  ⟦chain⟧ σ t (suc j) y = ⟦chain⟧ σ t j y

  private
    toRO : ∀ {ρ k g x y} → (val y ≈ rS ρ g k (val x)) × (ar y ≡ length (ins (B ρ))) × (dm y ≡ k) ×
           gpOK k (rgap ρ g) y → RO ρ k g x y
    toRO (v , a , d , q) = record { oval = v ; oar = a ; odm = d ; ogp = q }

    slotRO : ∀ x u (L : List Fm) (c : Cor) (R : List Fm) → ⟦ u ⟧ ≡ corSC c →
             ⟦ comp x (ids L ++ u ∷ ids R) ⟧ ≡ compS ⟦ x ⟧ (map idSC L ++ corSC c ∷ map idSC R)
    slotRO x u L c R e = cong (compS _) (trans (⟦slot⟧ L u R) (cong (λ z → map idSC L ++ z ∷ map idSC R) e))

  hiD-2 : ∀ x A k → dm x ≡ k → hiD (x ∷ idSC A ∷ []) ≡ k
  hiD-2 (sc v a zero g)    A .zero    refl = refl
  hiD-2 (sc v a (suc k) g) A .(suc k) refl = refl

  hiG-2 : ∀ x A k → dm x ≡ suc k → hiG (x ∷ idSC A ∷ []) ≡ gp x
  hiG-2 (sc v a (suc k) g) A .k refl = refl

  hiG-1 : ∀ x k → dm x ≡ suc k → hiG (x ∷ []) ≡ gp x
  hiG-1 (sc v a (suc k) g) .k refl = refl

  rmapSem : ∀ ρ {k g} u → RD ρ k g ⟦ u ⟧ → RO ρ k g ⟦ u ⟧ ⟦ rmap ρ u ⟧
  rmapSem (pairR L U W R Z) {k} {g} u rd
    rewrite slotRO u (mP U W) L (cm U W) R refl =
    toRO (slotSem {L} {cm U W} {R} {Z} ⟦ u ⟧ (rcell rd) (rdm rd) (rgp rd))
  rmapSem (probeR L Δ Θ R Z) {k} {g} u rd
    rewrite slotRO u (pP Δ Θ) L (cp Δ Θ) R refl =
    toRO (slotSem {L} {cp Δ Θ} {R} {Z} ⟦ u ⟧ (rcell rd) (rdm rd) (rgp rd))
  rmapSem (unitR L R Z) {k} {g} u rd
    rewrite slotRO u pt L cpt R refl =
    toRO (slotSem {L} {cpt} {R} {Z} ⟦ u ⟧ (rcell rd) (rdm rd) (rgp rd))
  rmapSem (evLR Φ A C) {k} {g} u rd with rcell rd
  ... | cellAt pre post sp len tx = record
    { oval = unit-r {P = []} {Y = A} {Q = pre ++ dsrc k ++ post}
               (retype (T-pc {P = A ∷ []} {Y = A \\ C} {Q = []} (T-evL A C) tx)
                       (cong (λ l → (A ∷ l) ▸ C) (++-[] (pre ++ dsrc k ++ post))))
    ; oar  = cong suc (trans (+-zero (ar ⟦ u ⟧)) (rar rd))
    ; odm  = hiD-1 ⟦ u ⟧ k (rdm rd)
    ; ogp  = gp-ev k (rdm rd) (rgp rd)
    }
    where
    gp-ev : ∀ k → dm ⟦ u ⟧ ≡ k → gpOK k g ⟦ u ⟧ → gpOK k (suc g) (sc _ _ _ (hiG (idSC A ∷ ⟦ u ⟧ ∷ [])))
    gp-ev zero    d q = tt
    gp-ev (suc k) d q = cong suc (trans (hiG-1 ⟦ u ⟧ k d) q)
  rmapSem (evRR Φ A C) {k} {g} u rd = record
    { oval = pc-cong 0 (unit-r {P = (C // A) ∷ []} {Y = A} {Q = []} (T-evR A C)) ≈-refl
    ; oar  = trans (cong (ar ⟦ u ⟧ +_) refl) (trans (cong (_+ 1) (rar rd)) (sym (length-++ Φ (A ∷ []))))
    ; odm  = hiD-2 ⟦ u ⟧ A k (rdm rd)
    ; ogp  = gp-ev k (rdm rd) (rgp rd)
    }
    where
    gp-ev : ∀ k → dm ⟦ u ⟧ ≡ k → gpOK k g ⟦ u ⟧ → gpOK k g (sc _ _ _ (hiG (⟦ u ⟧ ∷ idSC A ∷ [])))
    gp-ev zero    d q = tt
    gp-ev (suc k) d q = trans (hiG-2 ⟦ u ⟧ A k d) q

  -- an element of a type, as a cell at a given gap
  MemCell : ∀ A {x} g → Mem A x → gapIs g A → T (leq g (length (ins (baseM A)))) →
            CellAt (dim A) g (baseM A) (val x)
  MemCell (op M) g (tx , _ , _) _ bd =
    cellAt (take g (ins M)) (drop g (ins M)) (take-drop g (ins M)) (length-take g (ins M) bd)
           (retype tx (cong (_▸ out M) (sym (take-drop g (ins M)))))
  MemCell (hom m g′ A s t) g mx refl bd = cell mx

  MemMeta : ∀ A {x} g → Mem A x → gapIs g A → (ar x ≡ length (ins (baseM A))) × (dm x ≡ dim A) × gpOK (dim A) g x
  MemMeta (op M) g (_ , a , d) _ = a , d , tt
  MemMeta (hom m g′ A s t) g mx refl = mAr mx , mDm mx , mGp mx

  toRD : ∀ ρ A {x} k g → Mem A x → gapIs g A → T (leq g (length (ins (H ρ)))) →
         dim A ≡ k → baseM A ≡ H ρ → RD ρ k g x
  toRD ρ A {x} .(dim A) g mx ga bd refl eb = record
    { rcell = subst (λ M → CellAt (dim A) g M (val x)) eb
                (MemCell A g mx ga (subst (λ M → T (leq g (length (ins M)))) (sym eb) bd))
    ; rar = trans (fst (MemMeta A g mx ga)) (cong (λ M → length (ins M)) eb)
    ; rdm = fst (snd (MemMeta A g mx ga)) ; rgp = snd (snd (MemMeta A g mx ga)) }

  ----------------------------------------------------------------------
  -- The coherence terms

  record Inst (t : Tmpl) (φs : List Fm) (ts : List Tm) : Set where
    field
      iok   : T (okT t)
      iφ    : length φs ≡ nObj t
      its   : length ts ≡ nCtx t
      iargs : All2 (λ x A → Mem (sY (instS φs ts) A) ⟦ x ⟧) ts (ctx t)
  open Inst public

  module Here (ρ : Row) (g : Nat) (md : Mode) (φs : List Fm) (ts : List Tm) where
    τ  = instS φs ts
    φ  = nthF φs
    ρ′ = sRow φ ρ
    g′ = rgap ρ g
    cs = ⟦ ts ⟧s

    tt′ : Nat → Tmpl
    tt′ n = tmpl ρ g md n

    eg′ : rgap ρ′ g ≡ g′
    eg′ = rgap-sRow φ ρ g

    eH : sM φ (H ρ) ≡ H ρ′
    eH = sM-H φ ρ
    eB : sM φ (B ρ) ≡ B ρ′
    eB = sM-B φ ρ

    ball : Nat → SC
    ball n = nthS cs (pos n 0)

    module AtLevel (n : Nat) (I : Inst (tt′ n) φs ts) where
      t   = tt′ n
      bdH : T (leq g (length (ins (H ρ′))))
      bdH = H-bound φ ρ g (okT-bound ρ g md n (iok I))
      bdB : T (leq g′ (length (ins (B ρ′))))
      bdB = subst (λ h → T (leq h (length (ins (B ρ′))))) eg′ (rgap-bound ρ′ g bdH)

      entry : ∀ i {A} → lookup (ctx t) i ≡ just A → Mem (sY τ A) ⟦ nthT ts i ⟧
      entry i e = lookupAll2 (iargs I) i e

      Mb : Mem (sY τ (tyB t n)) (ball n)
      Mb = Mem-≡ (sY τ (tyB t n)) (⟦nthT⟧ ts (pos n 0)) (entry (pos n 0) (lookup-ball τ t n))

      ballCell : CellAt n (rgap ρ′ g) (B ρ′) (val (ball n))
      ballCell = cell-gap (sym eg′)
        (subst₂′ (λ k M → CellAt k g′ M (val (ball n))) (dim-tyB τ t n) (trans (base-tyB τ t n) eB)
          (MemCell (sY τ (tyB t n)) g′ Mb (gap-tyB τ t n)
             (subst (λ M → T (leq g′ (length (ins M)))) (sym (trans (base-tyB τ t n) eB)) bdB)))

      cval : V
      cval = rinvS ρ′ g n (val (ball n))

      cCell : CellAt n g (H ρ′) cval
      cCell = T-rinvS ρ′ bdH ballCell

      rr : rS ρ′ g n cval ≈ val (ball n)
      rr = rinv-r ρ′ bdH ballCell

      uRD : ∀ m {x} → Mem (sY τ (tyU t m)) x → RD ρ′ m g x
      uRD m mx = toRD ρ′ (sY τ (tyU t m)) m g mx (gap-tyU τ t m) bdH (dim-tyU τ t m) (trans (base-tyU τ t m) eH)

    -- c
    hereC : ∀ n → Inst (tt′ n) φs ts → Mem (sY τ (cgoal (tt′ n))) (hereS gc (tt′ n) φs cs)
    hereC zero I with cCell
      where open AtLevel zero I
    ... | cellAt pre post sp len ty =
      retype (retype ty (cong (_▸ out (H ρ′)) sp)) (cong (λ M → M) (sym (sM-H φ ρ))) ,
      cong (λ M → length (ins M)) (sym (sM-H φ ρ)) , refl
    hereC (suc m) I =
      mkHom m (sM φ (H ρ)) (dim-tyU τ t m) (base-tyU τ t m)
        (subst (λ M → CellAt (suc m) g M cval) (sym eH) cCell)
        (cong (λ M → length (ins M)) (sym eH)) refl refl (gap-tyU τ t m)
        Mu⁻ Mu⁺
        (≈-trans (face false {⟦ nthT ts (bM m) ⟧} (fS′ m (dim-tyB τ t m) Mb)) (≈-sym (u-β {uM m} {bM m} Mu⁻ Ma⁻)))
        (≈-trans (face true {⟦ nthT ts (bP m) ⟧} (fT′ m (dim-tyB τ t m) Mb)) (≈-sym (u-β {uP m} {bP m} Mu⁺ Ma⁺)))
        (λ e → ≈-trans (u-β {uM m} {bM m} Mu⁻ Ma⁻) (≈-trans (rinv-cong ρ′ g m (flat Mb e)) (≈-sym (u-β {uP m} {bP m} Mu⁺ Ma⁺))))
      where
      open AtLevel (suc m) I
      top : ∀ o → lookup (ctx t) (o + m * 6) ≡ lookup (block t m ++ tyB t (suc m) ∷ []) o
      top o = lookup-top τ t m o (tyB t (suc m) ∷ [])
      Mu⁻ = entry (uM m) (top 0)
      Mu⁺ = entry (uP m) (top 1)
      Ma⁻ = entry (aM m) (top 4)
      Ma⁺ = entry (aP m) (top 5)
      -- u^α from β^α through the collar
      u-β : ∀ {i j k} → Mem (sY τ (tyU t m)) ⟦ nthT ts i ⟧ →
            Mem (sY τ (hom inv g′ (tyRU t m) (rmap ρ (var i)) (chain t m (var j)))) k →
            val ⟦ nthT ts i ⟧ ≈ rinvS ρ′ g m (val ⟦ nthT ts j ⟧)
      u-β {i} {j} mu ma =
        ≈-trans (≈-sym (rinv-l ρ′ (rcell rd)))
        (rinv-cong ρ′ g m (≈-trans (≈-sym (oval (rmapSem ρ′ (nthT ts i) rd)))
                          (≈-trans (≡→≈ (cong (λ z → val ⟦ z ⟧) (sym (sT-rmap τ ρ (var i)))))
                          (≈-trans (flat ma refl) (≡→≈ (cong val (⟦chain⟧ τ t m (var j))))))))
        where rd = uRD m mu
      face : ∀ α {y} → pc (val (ball (suc m))) g′ (δ α m) ≈ val y →
             pc cval g (δ α m) ≈ rinvS ρ′ g m (val y)
      face α f = ≈-trans (rinv-face ρ′ α bdH ballCell)
                         (rinv-cong ρ′ g m (≈-trans (≡→≈ (cong (λ h → pc (val (ball (suc m))) h (δ α m)) eg′)) f))

    module Top (m : Nat) (I : Inst (tt′ (suc m)) φs ts) where
      open AtLevel (suc m) I public
      top : ∀ o → lookup (ctx t) (o + m * 6) ≡ lookup (block t m ++ tyB t (suc m) ∷ []) o
      top o = lookup-top τ t m o (tyB t (suc m) ∷ [])
      Mu⁻ = entry (uM m) (top 0)
      Mu⁺ = entry (uP m) (top 1)
      Ma⁻ = entry (aM m) (top 4)
      Ma⁺ = entry (aP m) (top 5)

      rmapU : ∀ i → Mem (sY τ (tyU t m)) ⟦ nthT ts i ⟧ →
              val ⟦ sT τ (rmap ρ (var i)) ⟧ ≈ rS ρ′ g m (val ⟦ nthT ts i ⟧)
      rmapU i mu = ≈-trans (≡→≈ (cong (λ z → val ⟦ z ⟧) (sT-rmap τ ρ (var i))))
                           (oval (rmapSem ρ′ (nthT ts i) (uRD m mu)))

      βr : ∀ {i j k} → Mem (sY τ (hom inv g′ (tyRU t m) (rmap ρ (var i)) (chain t m (var j)))) k →
           val ⟦ sT τ (rmap ρ (var i)) ⟧ ≈ val ⟦ nthT ts j ⟧
      βr {i} {j} ma = ≈-trans (flat ma refl) (≡→≈ (cong val (⟦chain⟧ τ t m (var j))))

    cS : Nat → SC
    cS n = hereS gc (tt′ n) φs cs

    R : Nat → SC
    R n = ⟦ rmap ρ′ (here (tt′ n) gc φs ts) ⟧

    rdC : ∀ n (I : Inst (tt′ n) φs ts) → RO ρ′ n g (cS n) (R n)
    rdC n I = rmapSem ρ′ (here (tt′ n) gc φs ts) (AtLevel.uRD n I n (hereC n I))

    -- r(c), in the type of the collars
    memRc : ∀ n (I : Inst (tt′ n) φs ts) → Mem (sY τ (tyRU (tt′ n) n)) (R n)
    memRc zero I with cell-≈ (≈-sym (oval (rdC zero I))) (T-rS ρ′ cCell)
      where open AtLevel zero I
    ... | cellAt pre post sp len ty =
      retype (retype ty (cong (_▸ out (B ρ′)) sp)) (sym eB) ,
      trans (oar (rdC zero I)) (cong (λ M → length (ins M)) (sym eB)) , odm (rdC zero I)
    memRc (suc m) I =
      mkHom m (sM φ (B ρ)) (dim-tyRU τ t m) (base-tyRU τ t m)
        (subst (λ M → CellAt (suc m) g′ M (val (R (suc m)))) (sym eB)
               (cell-gap eg′ (cell-≈ (≈-sym (oval rd)) (T-rS ρ′ cCell))))
        (trans (oar rd) (cong (λ M → length (ins M)) (sym eB))) (odm rd) (trans (ogp rd) eg′)
        (gap-tyRU τ t m) (memS Ma⁻) (memS Ma⁺)
        (face false {⟦ nthT ts (uM m) ⟧} (fS′ m (dim-tyU τ t m) Mc) (rmapU (uM m) Mu⁻))
        (face true {⟦ nthT ts (uP m) ⟧} (fT′ m (dim-tyU τ t m) Mc) (rmapU (uP m) Mu⁺))
        (λ e → ≈-trans (rmapU (uM m) Mu⁻) (≈-trans (rS-cong ρ′ g m (flat Mc e)) (≈-sym (rmapU (uP m) Mu⁺))))
      where
      open Top m I
      rd = rdC (suc m) I
      Mc = hereC (suc m) I
      face : ∀ α {y z} → pc cval g (δ α m) ≈ val y → z ≈ rS ρ′ g m (val y) →
             pc (val (R (suc m))) g′ (δ α m) ≈ z
      face α f q =
        ≈-trans (≡→≈ (cong (λ h → pc (val (R (suc m))) h (δ α m)) (sym eg′)))
        (≈-trans (pc-cong (rgap ρ′ g) (oval rd) ≈-refl)
        (≈-trans (r-face ρ′ α cCell)
        (≈-trans (rS-cong ρ′ g m f) (≈-sym q))))

    -- the ball, in the type of the collars
    memBRU : ∀ n (I : Inst (tt′ n) φs ts) → Mem (sY τ (tyRU (tt′ n) n)) (ball n)
    memBRU zero I = AtLevel.Mb zero I
    memBRU (suc m) I =
      mkHom m (sM φ (B ρ)) (dim-tyRU τ t m) (base-tyRU τ t m)
        (cell′ m (sM φ (B ρ)) (dim-tyB τ t m) (base-tyB τ t m) Mb)
        (trans (mAr Mb) (cong (λ M → length (ins M)) (base-tyB τ t m)))
        (trans (mDm Mb) (cong suc (dim-tyB τ t m))) (mGp Mb)
        (gap-tyRU τ t m) (memS Ma⁻) (memS Ma⁺)
        (≈-trans (fS′ m (dim-tyB τ t m) Mb) (≈-sym (βr {uM m} {bM m} Ma⁻)))
        (≈-trans (fT′ m (dim-tyB τ t m) Mb) (≈-sym (βr {uP m} {bP m} Ma⁺)))
        (λ e → ≈-trans (βr {uM m} {bM m} Ma⁻) (≈-trans (flat Mb e) (≈-sym (βr {uP m} {bP m} Ma⁺))))
      where open Top m I

    -- ε
    hereE : ∀ n → Inst (tt′ n) φs ts → Mem (sY τ (egoal (tt′ n))) (hereS gε (tt′ n) φs cs)
    hereE n I with ballCell
      where open AtLevel n I
    ... | cellAt pre post sp len ty =
      mkHom n (sM φ (B ρ)) (dim-tyRU τ t n) (base-tyRU τ t n)
        (subst (λ M → CellAt (suc n) g′ M dv) (sym eB)
               (cell-gap eg′ (cellAt pre post sp len (T-degen ty len))))
        (cong (λ M → length (ins M)) (sym eB)) refl eg′
        (gap-tyRU τ t n)
        (Mem-≡ (sY τ (tyRU t n)) (sym eqR) (memRc n I))
        (Mem-≡ (sY τ (tyRU t n)) (sym eqT) (memBRU n I))
        (≈-trans (fd false) (≈-trans (≈-sym srcV) (≡→≈ (cong val (sym eqR)))))
        (≈-trans (fd true) (≡→≈ (cong val (sym eqT))))
        (λ _ → ≈-trans (≡→≈ (cong val eqR)) (≈-trans srcV (≡→≈ (cong val (sym eqT)))))
      where
      open AtLevel n I
      dv = degen n (rgap ρ′ g) (val (ball n))
      eqR : ⟦ sT τ (rmap ρ (cterm t)) ⟧ ≡ R n
      eqR = cong ⟦_⟧ (trans (sT-rmap τ ρ (cterm t)) (cong (rmap ρ′) (sT-cterm t φs ts (iφ I) (its I))))
      eqT : ⟦ sT τ (chain t n (var (pos n 0))) ⟧ ≡ ball n
      eqT = trans (⟦chain⟧ τ t n (var (pos n 0))) (⟦nthT⟧ ts (pos n 0))
      srcV : val (R n) ≈ val (ball n)
      srcV = ≈-trans (oval (rdC n I)) rr
      fd : ∀ α → pc dv g′ (δ α n) ≈ val (ball n)
      fd α = ≈-trans (≡→≈ (cong (λ h → pc dv h (δ α n)) (sym eg′))) (face-degen α ty len)
