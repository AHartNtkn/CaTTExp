------------------------------------------------------------------------
-- D7f: every template of F.7.4 is well typed, for every row, gap,
-- mode and dimension.
--
-- Main result (no postulates):
--   templates-typed : ∀ t → T (wtGoal (ctx t) (cgoal t)) × T (wf (ctx t) (egoal t))
-- i.e. the generic context of every (GB-cut) / (GB-dcut) template is
-- well formed entry by entry, and both goals (c and ε) are well formed
-- cell types in it, for the type checker of Typing.agda (including its
-- stated typing rule for glue).  Examples.agda checked this by
-- evaluation for n ≤ 3; this module proves it for all n.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.TemplatesTyped where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Templates

------------------------------------------------------------------------
-- Arithmetic and list lemmas

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

lookup-B : ∀ {A : Set} (xs ys : List A) o → lookup (xs ++ ys) (o + length xs) ≡ lookup ys o
lookup-B []       ys o rewrite +-zero o = refl
lookup-B (x ∷ xs) ys o rewrite +-suc o (length xs) = lookup-B xs ys o

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true} _ = refl

map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

countHom-op : ∀ xs → countHom (map op xs) ≡ 0
countHom-op []       = refl
countHom-op (x ∷ xs) = countHom-op xs

baseM-op : ∀ xs → map baseM (map op xs) ≡ xs
baseM-op []       = refl
baseM-op (x ∷ xs) = cong (x ∷_) (baseM-op xs)

out-idTys : ∀ L → map out (idTys L) ≡ L
out-idTys []       = refl
out-idTys (x ∷ L)  = cong (x ∷_) (out-idTys L)

ins-idTys : ∀ L → concatIns (idTys L) ≡ L
ins-idTys []       = refl
ins-idTys (x ∷ L)  = cong (x ∷_) (ins-idTys L)

concatIns-++ : ∀ xs ys → concatIns (xs ++ ys) ≡ concatIns xs ++ concatIns ys
concatIns-++ []       ys = refl
concatIns-++ (x ∷ xs) ys rewrite concatIns-++ xs ys = sym (++-assoc (ins x) (concatIns xs) (concatIns ys))

eqTy-dim : ∀ A B → eqTy A B ≡ true → dim A ≡ dim B
eqTy-dim A B e = cong dim (eqTy-sound A B (subst T (sym e) tt))

------------------------------------------------------------------------
-- The arguments of the f-higher rows (pair, probe pair, unit)

argTys : List Fm → MTy → List Fm → List MTy
argTys L Mx R = idTys L ++ Mx ∷ idTys R

inferL-ids : ∀ Γ L → inferL Γ (ids L) ≡ just (map op (idTys L))
inferL-ids Γ []      = refl
inferL-ids Γ (A ∷ L) rewrite inferL-ids Γ L = refl

inferL-args : ∀ Γ L x Mx R → infer Γ x ≡ just (op Mx) →
              inferL Γ (ids L ++ x ∷ ids R) ≡ just (map op (argTys L Mx R))
inferL-args Γ [] x Mx R px rewrite px | inferL-ids Γ R = refl
inferL-args Γ (A ∷ L) x Mx R px rewrite inferL-args Γ L x Mx R px = refl

compOp-args : ∀ L Mx R Z →
  compOp ((L ++ out Mx ∷ R) ▸ Z) (argTys L Mx R) ≡ just ((L ++ ins Mx ++ R) ▸ Z)
compOp-args L Mx R Z
  rewrite map-++ out (idTys L) (Mx ∷ idTys R) | out-idTys L | out-idTys R
        | T→≡ (eqFms-refl (L ++ out Mx ∷ R))
        | concatIns-++ (idTys L) (Mx ∷ idTys R) | ins-idTys L | ins-idTys R = refl

------------------------------------------------------------------------
-- L1: r sends the H-tower to the B-tower

module _ (t : Tmpl) where
  private
    ρ = row t
    g = gap t
    m = mode t

  -- f-higher rows: rmap ρ x = comp x gs, with argument types ms
  liftF-tyU : ∀ gs ms → compOp (H ρ) ms ≡ just (B ρ) →
              (∀ x → rmap ρ x ≡ comp x gs) → rgap ρ g ≡ sumIns (take g ms) →
              ∀ k → liftF gs ms (tyU t k) ≡ just (tyRU t k)
  liftF-tyU gs ms hB hR hG zero rewrite hB = refl
  liftF-tyU gs ms hB hR hG (suc j)
    rewrite liftF-tyU gs ms hB hR hG j | hR (var (uM j)) | hR (var (uP j)) | hG = refl

  infer-fhigher : ∀ Γ gs ms → inferL Γ gs ≡ just (map op ms) →
                  compOp (H ρ) ms ≡ just (B ρ) →
                  (∀ x → rmap ρ x ≡ comp x gs) → rgap ρ g ≡ sumIns (take g ms) →
                  ∀ k x → infer Γ x ≡ just (tyU t k) → infer Γ (comp x gs) ≡ just (tyRU t k)
  infer-fhigher Γ gs ms pgs hB hR hG zero x px
    rewrite px | pgs | countHom-op ms | baseM-op ms | hB = refl
  infer-fhigher Γ gs ms pgs hB hR hG (suc j) x px
    rewrite px | pgs | countHom-op ms | baseM-op ms = liftF-tyU gs ms hB hR hG (suc j)

-- left evaluation: rmap x = comp (eL A C) (idt A ∷ x ∷ [])
liftG-evL : ∀ g m n Φ A C x M2 k →
  liftG (eL A C) (idt A ∷ x ∷ []) 1 ((A ∷ (A \\ C) ∷ []) ▸ C)
        (((A ∷ []) ▸ A) ∷ M2 ∷ []) (tyU (tmpl (evLR Φ A C) g m n) k)
  ≡ just (tyRU (tmpl (evLR Φ A C) g m n) k)
liftG-evL g m n Φ A C x M2 zero
  rewrite T→≡ (eqFms-refl (A ∷ (A \\ C) ∷ [])) | ++-[] Φ = refl
liftG-evL g m n Φ A C x M2 (suc j)
  rewrite liftG-evL g m n Φ A C x M2 j = refl

-- right evaluation: rmap x = comp (eR A C) (x ∷ idt A ∷ [])
liftG-evR : ∀ g m n Φ A C x M1 k →
  liftG (eR A C) (x ∷ idt A ∷ []) 0 (((C // A) ∷ A ∷ []) ▸ C)
        (M1 ∷ ((A ∷ []) ▸ A) ∷ []) (tyU (tmpl (evRR Φ A C) g m n) k)
  ≡ just (tyRU (tmpl (evRR Φ A C) g m n) k)
liftG-evR g m n Φ A C x M1 zero
  rewrite T→≡ (eqFms-refl ((C // A) ∷ A ∷ [])) = refl
liftG-evR g m n Φ A C x M1 (suc j)
  rewrite liftG-evR g m n Φ A C x M1 j = refl

infer-rmap : ∀ t Γ k x → infer Γ x ≡ just (tyU t k) →
             infer Γ (rmap (row t) x) ≡ just (tyRU t k)
infer-rmap t@(tmpl (pairR L U V R Z) g m n) Γ k x px =
  infer-fhigher t Γ (ids L ++ mP U V ∷ ids R) (argTys L ((U ∷ V ∷ []) ▸ (U ⊗ V)) R)
    (inferL-args Γ L (mP U V) _ R refl) (compOp-args L _ R Z) (λ _ → refl) refl k x px
infer-rmap t@(tmpl (probeR L Δ Θ R Z) g m n) Γ k x px =
  infer-fhigher t Γ (ids L ++ pP Δ Θ ∷ ids R) (argTys L ((rep Δ ∷ rep Θ ∷ []) ▸ rep (Δ ⊠ Θ)) R)
    (inferL-args Γ L (pP Δ Θ) _ R refl) (compOp-args L _ R Z) (λ _ → refl) refl k x px
infer-rmap t@(tmpl (unitR L R Z) g m n) Γ k x px =
  infer-fhigher t Γ (ids L ++ pt ∷ ids R) (argTys L ([] ▸ rep (disk 0)) R)
    (inferL-args Γ L pt _ R refl) (compOp-args L _ R Z) (λ _ → refl) refl k x px
infer-rmap (tmpl (evLR Φ A C) g m n) Γ zero x px
  rewrite px | T→≡ (eqFms-refl (A ∷ (A \\ C) ∷ [])) | ++-[] Φ = refl
infer-rmap (tmpl (evLR Φ A C) g m n) Γ (suc j) x px
  rewrite px = liftG-evL g m n Φ A C x _ (suc j)
infer-rmap (tmpl (evRR Φ A C) g m n) Γ zero x px
  rewrite px | T→≡ (eqFms-refl ((C // A) ∷ A ∷ [])) = refl
infer-rmap (tmpl (evRR Φ A C) g m n) Γ (suc j) x px
  rewrite px = liftG-evR g m n Φ A C x _ (suc j)

------------------------------------------------------------------------
-- Booleans on Nat

leq-refl : ∀ k → leq k k ≡ true
leq-refl zero    = refl
leq-refl (suc k) = leq-refl k

leq-sucfalse : ∀ i → leq (suc i) i ≡ false
leq-sucfalse zero    = refl
leq-sucfalse (suc i) = leq-sucfalse i

leq-gt : ∀ i d → leq (suc (i + d)) i ≡ false
leq-gt zero    d = refl
leq-gt (suc i) d = leq-gt i d

leq-gt2 : ∀ i d → leq (suc (suc (i + d))) i ≡ false
leq-gt2 zero    d = refl
leq-gt2 (suc i) d = leq-gt2 i d

no-eq : ∀ i d → i ≡ suc (i + d) → ⊥
no-eq zero    d ()
no-eq (suc i) d e = no-eq i d (cong pr e)
  where pr : Nat → Nat
        pr zero    = zero
        pr (suc k) = k

bool-false : (b : Bool) → (b ≡ true → ⊥) → b ≡ false
bool-false true  ne = ⊥-elim (ne refl)
bool-false false ne = refl

eqTy-false : ∀ A B → (dim A ≡ dim B → ⊥) → eqTy A B ≡ false
eqTy-false A B ne = bool-false (eqTy A B) (λ e → ne (eqTy-dim A B e))

------------------------------------------------------------------------
-- L2: collar chains, and L3: lookups, for a fixed template

module Fixed (t : Tmpl) where
  private
    ρ  = row t
    g  = gap t
    m  = mode t
    g′ = rgap (row t) (gap t)

  tyAx : Nat → Nat → Nat → CTy
  tyAx j uu bb = hom inv g′ (tyRU t j) (rmap ρ (var uu)) (chain t j (var bb))

  -- the type of chain j y for y : tyB k (k ≥ j): levels below j are
  -- moved to the H side by the collars, levels from j up keep b's
  mix : Nat → Nat → CTy
  mix j zero    = op (B ρ)
  mix j (suc k) = if leq (suc k) j then tyRU t (suc k)
                  else hom m g′ (mix j k) (chain t j (var (bM k))) (chain t j (var (bP k)))

  dim-tyRU : ∀ k → dim (tyRU t k) ≡ k
  dim-tyRU zero    = refl
  dim-tyRU (suc k) = cong suc (dim-tyRU k)

  dim-mix : ∀ j k → dim (mix j k) ≡ k
  dim-mix j zero = refl
  dim-mix j (suc k) with leq (suc k) j
  ... | true  = dim-tyRU (suc k)
  ... | false = cong suc (dim-mix j k)

  mix-low : ∀ k → mix k k ≡ tyRU t k
  mix-low zero    = refl
  mix-low (suc k) rewrite leq-refl k = refl

  mix0 : ∀ k → mix 0 k ≡ tyB t k
  mix0 zero    = refl
  mix0 (suc k) rewrite mix0 k = refl

  glue-step : ∀ i d →
    glueTy (var (aM i)) (var (aP i)) (tyRU t i) (chain t i (var (bM i))) (chain t i (var (bP i)))
           (rmap ρ (var (uM i))) (rmap ρ (var (uP i))) (mix i (suc (i + d)))
    ≡ just (mix (suc i) (suc (i + d)))
  glue-step i zero
    rewrite +-zero i | leq-sucfalse i | mix-low i | leq-refl i
          | T→≡ (eqTy-refl (tyRU t i))
          | T→≡ (eqTm-refl (chain t i (var (bM i))))
          | T→≡ (eqTm-refl (chain t i (var (bP i)))) = refl
  glue-step i (suc d)
    rewrite +-suc i d | leq-gt2 i d
          | eqTy-false (mix i (suc (i + d))) (tyRU t i)
              (λ e → no-eq i d (sym (trans (sym (dim-mix i (suc (i + d)))) (trans e (dim-tyRU i)))))
          | glue-step i d | leq-gt i d = refl

  HypA : Ctx → Nat → Set
  HypA Γ j = ∀ i e → j ≡ suc (i + e) →
             (lookup Γ (aM i) ≡ just (tyAx i (uM i) (bM i))) × (lookup Γ (aP i) ≡ just (tyAx i (uP i) (bP i)))

  chain-typed : ∀ j Γ → HypA Γ j → ∀ d y → infer Γ y ≡ just (tyB t (j + d)) →
                infer Γ (chain t j y) ≡ just (mix j (j + d))
  chain-typed zero Γ h d y py rewrite py | mix0 d = refl
  chain-typed (suc i) Γ h d y py
    with h i 0 (cong suc (sym (+-zero i)))
  ... | (la , lb)
    rewrite la | lb
          | chain-typed i Γ (λ i′ e p → h i′ (suc e) (cong suc (trans p (sym (+-suc i′ e)))))
                        (suc d) y (trans py (cong (λ q → just (tyB t q)) (sym (+-suc i d))))
          | +-suc i d
          | T→≡ (==ℕ-refl g′) | T→≡ (eqTy-refl (tyRU t i))
    = glue-step i d

  -- lookups
  length-levels : ∀ j → length (levels t j) ≡ j * 6
  length-levels zero = refl
  length-levels (suc j)
    rewrite length-++ (levels t j) (block t j) | length-levels j = +-comm (j * 6) 6

  lookup-at : ∀ J R o → lookup (levels t J ++ R) (pos J o) ≡ lookup R o
  lookup-at J R o =
    trans (cong (λ q → lookup (levels t J ++ R) (o + q)) (sym (length-levels J)))
          (lookup-B (levels t J) R o)

  levels-ext : ∀ i d → Σ Ctx (λ M → levels t (suc (i + d)) ≡ levels t i ++ (block t i ++ M))
  levels-ext i zero rewrite +-zero i = [] , cong (levels t i ++_) (sym (++-[] (block t i)))
  levels-ext i (suc d) rewrite +-suc i d with levels-ext i d
  ... | M , e = (M ++ block t (suc (i + d))) ,
    trans (cong (_++ block t (suc (i + d))) e)
      (trans (++-assoc (levels t i) (block t i ++ M) (block t (suc (i + d))))
             (cong (levels t i ++_) (++-assoc (block t i) M (block t (suc (i + d))))))

  Avail : Ctx → Nat → Set
  Avail Γ J = ∀ i d → J ≡ suc (i + d) → ∀ o → Σ Ctx (λ Q → lookup Γ (pos i o) ≡ lookup (block t i ++ Q) o)

  availL : ∀ J R → Avail (levels t J ++ R) J
  availL J R i d refl o with levels-ext i d
  ... | M , e rewrite e | ++-assoc (levels t i) (block t i ++ M) R =
    (M ++ R) , trans (lookup-at i ((block t i ++ M) ++ R) o)
                     (cong (λ q → lookup q o) (++-assoc (block t i) M R))

  availL′ : ∀ J → Avail (levels t J) J
  availL′ J = subst (λ Γ → Avail Γ J) (++-[] (levels t J)) (availL J [])

  hypA : ∀ Γ J → Avail Γ J → HypA Γ J
  hypA Γ J av i e p with av i e p 4 | av i e p 5
  ... | (_ , l4) | (_ , l5) = l4 , l5

  ------------------------------------------------------------------------
  -- well-formedness of the towers

  T-just : ∀ Γ n A → lookup Γ n ≡ just A → T (eqMaybeTy (infer Γ (var n)) A)
  T-just Γ n A e = subst (λ q → T (eqMaybeTy q A)) (sym e) (eqTy-refl A)

  T-inf : ∀ {Γ} x A → infer Γ x ≡ just A → T (eqMaybeTy (infer Γ x) A)
  T-inf x A e = subst (λ q → T (eqMaybeTy q A)) (sym e) (eqTy-refl A)

  wfU : ∀ Γ J → Avail Γ J → ∀ k d → J ≡ k + d → T (wf Γ (tyU t k))
  wfU Γ J av zero d p = tt
  wfU Γ J av (suc i) d p with av i d p 0 | av i d p 1
  ... | (_ , l0) | (_ , l1) =
    ∧-intro (wfU Γ J av i (suc d) (trans p (sym (+-suc i d))))
      (∧-intro (T-just Γ (uM i) (tyU t i) l0) (T-just Γ (uP i) (tyU t i) l1))

  wfB : ∀ Γ J → Avail Γ J → ∀ k d → J ≡ k + d → T (wf Γ (tyB t k))
  wfB Γ J av zero d p = tt
  wfB Γ J av (suc i) d p with av i d p 2 | av i d p 3
  ... | (_ , l2) | (_ , l3) =
    ∧-intro (wfB Γ J av i (suc d) (trans p (sym (+-suc i d))))
      (∧-intro (T-just Γ (bM i) (tyB t i) l2) (T-just Γ (bP i) (tyB t i) l3))

  wfRU : ∀ Γ J → Avail Γ J → ∀ k d → J ≡ k + d → T (wf Γ (tyRU t k))
  wfRU Γ J av zero d p = tt
  wfRU Γ J av (suc i) d p with av i d p 0 | av i d p 1
  ... | (_ , l0) | (_ , l1) =
    ∧-intro (wfRU Γ J av i (suc d) (trans p (sym (+-suc i d))))
      (∧-intro (T-inf (rmap ρ (var (uM i))) (tyRU t i) (infer-rmap t Γ i (var (uM i)) l0))
               (T-inf (rmap ρ (var (uP i))) (tyRU t i) (infer-rmap t Γ i (var (uP i)) l1)))

  wfA : ∀ Γ j uu bb → Avail Γ j → lookup Γ uu ≡ just (tyU t j) → lookup Γ bb ≡ just (tyB t j) →
        T (wf Γ (tyAx j uu bb))
  wfA Γ j uu bb av lu lb =
    ∧-intro (wfRU Γ j av j 0 (sym (+-zero j)))
      (∧-intro (T-inf (rmap ρ (var uu)) (tyRU t j) (infer-rmap t Γ j (var uu) lu))
               (T-inf (chain t j (var bb)) (tyRU t j)
                  (trans (chain-typed j Γ (hypA Γ j av) 0 (var bb)
                            (trans lb (cong (λ q → just (tyB t q)) (sym (+-zero j)))))
                         (cong just (trans (cong (mix j) (+-zero j)) (mix-low j))))))

  ------------------------------------------------------------------------
  -- the context, entry by entry

  wfCtxFrom-++ : ∀ acc xs ys → T (wfCtxFrom acc xs) → T (wfCtxFrom (acc ++ xs) ys) →
                 T (wfCtxFrom acc (xs ++ ys))
  wfCtxFrom-++ acc [] ys _ q = subst (λ Γ → T (wfCtxFrom Γ ys)) (++-[] acc) q
  wfCtxFrom-++ acc (x ∷ xs) ys p q =
    ∧-intro (∧-fst p)
      (wfCtxFrom-++ (acc ++ x ∷ []) xs ys (∧-snd {wf acc x} p)
        (subst (λ Γ → T (wfCtxFrom Γ ys)) (sym (++-assoc acc (x ∷ []) xs)) q))

  step : ∀ J P x xs → T (wf (levels t J ++ P) x) →
         T (wfCtxFrom (levels t J ++ (P ++ x ∷ [])) xs) → T (wfCtxFrom (levels t J ++ P) (x ∷ xs))
  step J P x xs w r = ∧-intro w (subst (λ Γ → T (wfCtxFrom Γ xs)) (sym (++-assoc (levels t J) P (x ∷ []))) r)

  block-ok : ∀ j → T (wfCtxFrom (levels t j) (block t j))
  block-ok j =
    subst (λ Γ → T (wfCtxFrom Γ (block t j))) (++-[] (levels t j))
    (step j [] (tyU t j) (u ∷ b ∷ b ∷ a4 ∷ a5 ∷ []) (wfU _ j (availL j []) j 0 (sym (+-zero j)))
    (step j (u ∷ []) (tyU t j) (b ∷ b ∷ a4 ∷ a5 ∷ []) (wfU _ j (availL j _) j 0 (sym (+-zero j)))
    (step j (u ∷ u ∷ []) (tyB t j) (b ∷ a4 ∷ a5 ∷ []) (wfB _ j (availL j _) j 0 (sym (+-zero j)))
    (step j (u ∷ u ∷ b ∷ []) (tyB t j) (a4 ∷ a5 ∷ []) (wfB _ j (availL j _) j 0 (sym (+-zero j)))
    (step j P4 (tyAx j (uM j) (bM j)) (a5 ∷ [])
       (wfA _ j (uM j) (bM j) (availL j P4) (lookup-at j P4 0) (lookup-at j P4 2))
    (step j P5 (tyAx j (uP j) (bP j)) []
       (wfA _ j (uP j) (bP j) (availL j P5) (lookup-at j P5 1) (lookup-at j P5 3))
    tt))))))
    where
    u = tyU t j
    b = tyB t j
    a4 = tyAx j (uM j) (bM j)
    a5 = tyAx j (uP j) (bP j)
    P4 = u ∷ u ∷ b ∷ b ∷ []
    P5 = u ∷ u ∷ b ∷ b ∷ tyAx j (uM j) (bM j) ∷ []

  wf-levels : ∀ J → T (wfCtxFrom [] (levels t J))
  wf-levels zero    = tt
  wf-levels (suc j) = wfCtxFrom-++ [] (levels t j) (block t j) (wf-levels j) (block-ok j)

------------------------------------------------------------------------
-- The theorem

here-ok : ∀ Γ A → T (wf Γ A) → infer Γ (here A) ≡ just A
here-ok Γ A p rewrite T→≡ p = refl

templates-typed : ∀ t → T (wtGoal (ctx t) (cgoal t)) × T (wf (ctx t) (egoal t))
templates-typed t = ∧-intro wfctx wfc , wfe
  where
  open Fixed t
  n = dimn t
  Γ = levels t n ++ (tyB t n ∷ [])
  av : Avail Γ n
  av = availL n (tyB t n ∷ [])
  wfctx : T (wfCtxFrom [] Γ)
  wfctx = wfCtxFrom-++ [] (levels t n) (tyB t n ∷ []) (wf-levels n)
            (∧-intro (wfB (levels t n) n (availL′ n) n 0 (sym (+-zero n))) tt)
  wfc : T (wf Γ (tyU t n))
  wfc = wfU Γ n av n 0 (sym (+-zero n))
  lb : lookup Γ (pos n 0) ≡ just (tyB t (n + 0))
  lb = trans (lookup-at n (tyB t n ∷ []) 0) (cong (λ q → just (tyB t q)) (sym (+-zero n)))
  wfe : T (wf Γ (egoal t))
  wfe = ∧-intro (wfRU Γ n av n 0 (sym (+-zero n)))
          (∧-intro (T-inf (rmap (row t) (here (tyU t n))) (tyRU t n)
                      (infer-rmap t Γ n (here (tyU t n)) (here-ok Γ (tyU t n) wfc)))
                   (T-inf (chain t n (var (pos n 0))) (tyRU t n)
                      (trans (chain-typed n Γ (hypA Γ n av) 0 (var (pos n 0)) lb)
                             (cong just (trans (cong (mix n) (+-zero n)) (mix-low n))))))
