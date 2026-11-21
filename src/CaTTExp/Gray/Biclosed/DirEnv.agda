------------------------------------------------------------------------
-- D7g, generic part: an interpretation of the generic context of a
-- directed template, in any model of the biclosed kernel.
--
-- Given a row ρ, a gap g of H and a tower of cells of H at gap g,
--   uv α j : a j-cell of H (α = false: the lower one, true: the upper),
-- whose faces are the two cells one level down, the context
-- ctx (tmpl ρ g dir (suc k)) is satisfied by
--   u⁻_j, u⁺_j ↦ uv false j, uv true j
--   β⁻_j, β⁺_j ↦ r(u⁻_j), r(u⁺_j)
--   a⁻_j, a⁺_j ↦ the degenerate cells on r(u±_j)
--   b          ↦ r(uv false (suc k))
-- (Theorem S's reading of inv is flat, and the collars here are flat).
-- By soundness (Soundness.agda), a derivable reverse goal u⁺ ⇒ u⁻ is
-- then interpreted by a (k+1)-cell of H at gap g whose source face is
-- uv true k and whose target face is uv false k (reverse-cell).
-- No postulates.
------------------------------------------------------------------------
open import CaTTExp.Gray.Biclosed.Model

module CaTTExp.Gray.Biclosed.DirEnv (𝔐 : Model) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.ListLemmas
open import CaTTExp.Gray.Biclosed.Templates
  using () renaming (dim-tyU to dimU; baseM-tyU to baseU)
open import Agda.Builtin.Nat using (_*_)
open Model 𝔐
open import CaTTExp.Gray.Biclosed.ModelFacts 𝔐
open import CaTTExp.Gray.Biclosed.RowSem 𝔐
open import CaTTExp.Gray.Biclosed.Sem 𝔐
open import CaTTExp.Gray.Biclosed.SemHere 𝔐
open import CaTTExp.Gray.Biclosed.Soundness using (soundness)

------------------------------------------------------------------------
-- Arithmetic and lookup

private
  T-≡′ : ∀ {b} → T b → b ≡ true
  T-≡′ {true} _ = refl

  leq-pred : ∀ j n → T (leq (suc j) n) → T (leq j n)
  leq-pred zero    n       _ = tt
  leq-pred (suc j) zero    ()
  leq-pred (suc j) (suc n) p = leq-pred j n p

  lt-ne : ∀ j n → T (leq (suc j) n) → (j ==ℕ n) ≡ false
  lt-ne zero    zero    ()
  lt-ne zero    (suc n) _ = refl
  lt-ne (suc j) zero    ()
  lt-ne (suc j) (suc n) p = lt-ne j n p

  leq-refl″ : ∀ n → T (leq n n)
  leq-refl″ zero    = tt
  leq-refl″ (suc n) = leq-refl″ n

  six : ∀ o m → o + (6 + m) ≡ 6 + (o + m)
  six o m = trans (sym (+-assoc o 6 m)) (trans (cong (_+ m) (+-comm o 6)) (+-assoc 6 o m))

lookup-split : ∀ {X : Set} (xs ys : List X) i {a} → lookup (xs ++ ys) i ≡ just a →
               (lookup xs i ≡ just a) ⊎′ Σ Nat (λ k → (i ≡ length xs + k) × (lookup ys k ≡ just a))
lookup-split []       ys i       e = inr (i , refl , e)
lookup-split (x ∷ xs) ys zero    e = inl e
lookup-split (x ∷ xs) ys (suc i) e with lookup-split xs ys i e
... | inl p             = inl p
... | inr (k , refl , p) = inr (k , refl , p)

------------------------------------------------------------------------
-- The environment

module Env (ρ : Row) (g k : Nat) (uv : Bool → Nat → V)
           (uc : ∀ α j → CellAt j g (H ρ) (uv α j))
           (uf : ∀ α β j → pc (uv α (suc j)) g (δ β j) ≈ uv β j) where

  n : Nat
  n = suc k

  t : Tmpl
  t = tmpl ρ g dir n

  g′ nH nB : Nat
  g′ = rgap ρ g
  nH = length (ins (H ρ))
  nB = length (ins (B ρ))

  rU : Bool → Nat → V
  rU α j = rS ρ g j (uv α j)

  Uc Bc Ac : Bool → Nat → SC
  Uc α j = sc (uv α j) nH j g
  Bc α j = sc (rU α j) nB j g′
  Ac α j = sc (degen j g′ (rU α j)) nB (suc j) g′

  E : Nat → Nat → SC
  E j zero                                     = if j ==ℕ n then Bc false n else Uc false j
  E j (suc zero)                               = Uc true j
  E j (suc (suc zero))                         = Bc false j
  E j (suc (suc (suc zero)))                   = Bc true j
  E j (suc (suc (suc (suc zero))))             = Ac false j
  E j (suc (suc (suc (suc (suc zero)))))       = Ac true j
  E j (suc (suc (suc (suc (suc (suc i))))))    = E (suc j) i

  ε : Nat → SC
  ε = E 0

  open Interp ε

  E-pos : ∀ a j o → E a (o + j * 6) ≡ E (a + j) o
  E-pos a zero    o = trans (cong (E a) (+-zero o)) (cong (λ b → E b o) (sym (+-zero a)))
  E-pos a (suc j) o =
    trans (cong (E a) (six o (j * 6)))
          (trans (E-pos (suc a) j o) (cong (λ b → E b o) (sym (+-suc a j))))

  ε-at : ∀ j o → ε (o + j * 6) ≡ E j o
  ε-at j o = E-pos 0 j o

  εuM : ∀ j → T (leq (suc j) n) → ε (uM j) ≡ Uc false j
  εuM j h = trans (ε-at j 0) (cong (λ b → if b then Bc false n else Uc false j) (lt-ne j n h))

  εuP : ∀ j → ε (uP j) ≡ Uc true j
  εuP j = ε-at j 1

  εbM : ∀ j → ε (bM j) ≡ Bc false j
  εbM j = ε-at j 2

  εbP : ∀ j → ε (bP j) ≡ Bc true j
  εbP j = ε-at j 3

  εball : ε (pos n 0) ≡ Bc false n
  εball = trans (ε-at n 0) (cong (λ b → if b then Bc false n else Uc false n) (T-≡′ (==ℕ-refl n)))

  ----------------------------------------------------------------------
  -- Shapes of the generic types

  dB : ∀ j → dim (tyB t j) ≡ j
  dB zero    = refl
  dB (suc j) = cong suc (dB j)

  dR : ∀ j → dim (tyRU t j) ≡ j
  dR zero    = refl
  dR (suc j) = cong suc (dR j)

  bB : ∀ j → baseM (tyB t j) ≡ B ρ
  bB zero    = refl
  bB (suc j) = bB j

  bR : ∀ j → baseM (tyRU t j) ≡ B ρ
  bR zero    = refl
  bR (suc j) = bR j

  gU : ∀ j → gapIs g (tyU t j)
  gU zero    = tt
  gU (suc j) = refl

  gB : ∀ j → gapIs g′ (tyB t j)
  gB zero    = tt
  gB (suc j) = refl

  gR : ∀ j → gapIs g′ (tyRU t j)
  gR zero    = tt
  gR (suc j) = refl

  gpU : ∀ α j → gpOK j g (Uc α j)
  gpU α zero    = tt
  gpU α (suc j) = refl

  gpB : ∀ α j → gpOK j g′ (Bc α j)
  gpB α zero    = tt
  gpB α (suc j) = refl

  fix : ∀ {h} A {j M x} → dim A ≡ j → baseM A ≡ M → CellAt (suc j) h M x → CellAt (suc (dim A)) h (baseM A) x
  fix A refl refl c = c

  dfix : ∀ {h} x α A {j} → dim A ≡ j → pc x h (δ α (dim A)) ≈ pc x h (δ α j)
  dfix x α A refl = ≈-refl

  rdU : ∀ α j → RD ρ j g (Uc α j)
  rdU α j = record { rcell = uc α j ; rar = refl ; rdm = refl ; rgp = gpU α j }

  typ0 : ∀ {h M x} → CellAt 0 h M x → x ∶ M
  typ0 {M = M} (cellAt pre post sp len ty) = retype ty (cong (_▸ out M) sp)

  degen-cell : ∀ {j M w} → CellAt j g′ M w → CellAt (suc j) g′ M (degen j g′ w)
  degen-cell (cellAt pre post sp len ty) = cellAt pre post sp len (T-degen ty len)

  degen-face : ∀ {j M w} α → CellAt j g′ M w → pc (degen j g′ w) g′ (δ α j) ≈ w
  degen-face α (cellAt pre post sp len ty) = face-degen α ty len

  chain-sem : ∀ j y → ⟦ chain t j y ⟧ ≡ ⟦ y ⟧
  chain-sem zero    y = refl
  chain-sem (suc j) y = chain-sem j y

  ----------------------------------------------------------------------
  -- Each entry is an element of its type

  MemU : ∀ α j → T (leq j n) → Mem (tyU t j) (Uc α j)
  MemU α zero    h = typ0 (uc α 0) , refl , refl
  MemU α (suc i) h = record
    { cell = fix (tyU t i) (dimU t i) (baseU t i) (uc α (suc i))
    ; mAr  = cong (λ M → length (ins M)) (sym (baseU t i))
    ; mDm  = cong suc (sym (dimU t i))
    ; mGp  = refl
    ; gapA = gU i
    ; memS = subst (Mem (tyU t i)) (sym (εuM i h)) (MemU false i (leq-pred i n h))
    ; memT = subst (Mem (tyU t i)) (sym (εuP i)) (MemU true i (leq-pred i n h))
    ; fS   = ≈-trans (dfix (uv α (suc i)) false (tyU t i) (dimU t i))
               (≈-trans (uf α false i) (≡→≈ (cong val (sym (εuM i h)))))
    ; fT   = ≈-trans (dfix (uv α (suc i)) true (tyU t i) (dimU t i))
               (≈-trans (uf α true i) (≡→≈ (cong val (sym (εuP i)))))
    ; flat = λ ()
    }

  MemB : ∀ α j → Mem (tyB t j) (Bc α j)
  MemB α zero    = typ0 (T-rS ρ (uc α 0)) , refl , refl
  MemB α (suc i) = record
    { cell = fix (tyB t i) (dB i) (bB i) (T-rS ρ (uc α (suc i)))
    ; mAr  = cong (λ M → length (ins M)) (sym (bB i))
    ; mDm  = cong suc (sym (dB i))
    ; mGp  = refl
    ; gapA = gB i
    ; memS = subst (Mem (tyB t i)) (sym (εbM i)) (MemB false i)
    ; memT = subst (Mem (tyB t i)) (sym (εbP i)) (MemB true i)
    ; fS   = ≈-trans (dfix (rU α (suc i)) false (tyB t i) (dB i))
               (≈-trans (r-face ρ false (uc α (suc i)))
               (≈-trans (rS-cong ρ g i (uf α false i)) (≡→≈ (cong val (sym (εbM i))))))
    ; fT   = ≈-trans (dfix (rU α (suc i)) true (tyB t i) (dB i))
               (≈-trans (r-face ρ true (uc α (suc i)))
               (≈-trans (rS-cong ρ g i (uf α true i)) (≡→≈ (cong val (sym (εbP i))))))
    ; flat = λ ()
    }

  -- r of a lower or upper u, as computed by the interpretation of rmap
  rmapU : ∀ α j ui → ε ui ≡ Uc α j → val ⟦ rmap ρ (var ui) ⟧ ≈ rU α j
  rmapU α j ui e =
    ≈-trans (oval (rmapSem ε ρ (var ui) (subst (RD ρ j g) (sym e) (rdU α j))))
            (rS-cong ρ g j (≡→≈ (cong val e)))

  MemRU : ∀ j y α → T (leq j n) → val y ≈ rU α j → ar y ≡ nB → dm y ≡ j → gpOK j g′ y →
          Mem (tyRU t j) y
  MemRU zero    y α h v a d q = ∶-≈ (≈-sym v) (typ0 (T-rS ρ (uc α 0))) , a , d
  MemRU (suc i) y α h v a d q = record
    { cell = fix (tyRU t i) (dR i) (bR i) (cell-≈ (≈-sym v) (T-rS ρ (uc α (suc i))))
    ; mAr  = trans a (cong (λ M → length (ins M)) (sym (bR i)))
    ; mDm  = trans d (cong suc (sym (dR i)))
    ; mGp  = q
    ; gapA = gR i
    ; memS = MemRU i ⟦ rmap ρ (var (uM i)) ⟧ false (leq-pred i n h) (rmapU false i (uM i) (εuM i h))
               (oar roM) (odm roM) (ogp roM)
    ; memT = MemRU i ⟦ rmap ρ (var (uP i)) ⟧ true (leq-pred i n h) (rmapU true i (uP i) (εuP i))
               (oar roP) (odm roP) (ogp roP)
    ; fS   = ≈-trans (dfix (val y) false (tyRU t i) (dR i))
               (≈-trans (pc-cong g′ v ≈-refl)
               (≈-trans (r-face ρ false (uc α (suc i)))
               (≈-trans (rS-cong ρ g i (uf α false i)) (≈-sym (rmapU false i (uM i) (εuM i h))))))
    ; fT   = ≈-trans (dfix (val y) true (tyRU t i) (dR i))
               (≈-trans (pc-cong g′ v ≈-refl)
               (≈-trans (r-face ρ true (uc α (suc i)))
               (≈-trans (rS-cong ρ g i (uf α true i)) (≈-sym (rmapU true i (uP i) (εuP i))))))
    ; flat = λ ()
    }
    where
    roM = rmapSem ε ρ (var (uM i)) (subst (RD ρ i g) (sym (εuM i h)) (rdU false i))
    roP = rmapSem ε ρ (var (uP i)) (subst (RD ρ i g) (sym (εuP i)) (rdU true i))

  MemA : ∀ α j ui bi → ε ui ≡ Uc α j → ε bi ≡ Bc α j → T (leq j n) →
         Mem (hom inv g′ (tyRU t j) (rmap ρ (var ui)) (chain t j (var bi))) (Ac α j)
  MemA α j ui bi eu eb h = record
    { cell = fix (tyRU t j) (dR j) (bR j) (degen-cell (T-rS ρ (uc α j)))
    ; mAr  = cong (λ M → length (ins M)) (sym (bR j))
    ; mDm  = cong suc (sym (dR j))
    ; mGp  = refl
    ; gapA = gR j
    ; memS = MemRU j ⟦ rmap ρ (var ui) ⟧ α h (rmapU α j ui eu) (oar ro) (odm ro) (ogp ro)
    ; memT = subst (Mem (tyRU t j)) (sym ech) (MemRU j (Bc α j) α h ≈-refl refl refl (gpB α j))
    ; fS   = ≈-trans (dfix (degen j g′ (rU α j)) false (tyRU t j) (dR j))
               (≈-trans (degen-face false (T-rS ρ (uc α j))) (≈-sym (rmapU α j ui eu)))
    ; fT   = ≈-trans (dfix (degen j g′ (rU α j)) true (tyRU t j) (dR j))
               (≈-trans (degen-face true (T-rS ρ (uc α j))) (≡→≈ (cong val (sym ech))))
    ; flat = λ _ → ≈-trans (rmapU α j ui eu) (≡→≈ (cong val (sym ech)))
    }
    where
    ro  = rmapSem ε ρ (var ui) (subst (RD ρ j g) (sym eu) (rdU α j))
    ech : ⟦ chain t j (var bi) ⟧ ≡ Bc α j
    ech = trans (chain-sem j (var bi)) eb

  ----------------------------------------------------------------------
  -- The environment satisfies the generic context

  length-levels : ∀ m → length (levels t m) ≡ m * 6
  length-levels zero    = refl
  length-levels (suc m) =
    trans (length-++ (levels t m) (block t m)) (trans (cong (_+ 6) (length-levels m)) (+-comm (m * 6) 6))

  blockMem : ∀ m → T (leq (suc m) n) → ∀ o {A} → lookup (block t m) o ≡ just A → Mem A (E m o)
  blockMem m h zero refl =
    subst (Mem (tyU t m)) (sym (cong (λ b → if b then Bc false n else Uc false m) (lt-ne m n h)))
          (MemU false m (leq-pred m n h))
  blockMem m h (suc zero) refl = MemU true m (leq-pred m n h)
  blockMem m h (suc (suc zero)) refl = MemB false m
  blockMem m h (suc (suc (suc zero))) refl = MemB true m
  blockMem m h (suc (suc (suc (suc zero)))) refl =
    MemA false m (uM m) (bM m) (εuM m h) (εbM m) (leq-pred m n h)
  blockMem m h (suc (suc (suc (suc (suc zero))))) refl =
    MemA true m (uP m) (bP m) (εuP m) (εbP m) (leq-pred m n h)
  blockMem m h (suc (suc (suc (suc (suc (suc o)))))) ()

  levelsMem : ∀ m → T (leq m n) → ∀ i {A} → lookup (levels t m) i ≡ just A → Mem A (ε i)
  levelsMem zero    h i ()
  levelsMem (suc m) h i {A} e with lookup-split (levels t m) (block t m) i e
  ... | inl p              = levelsMem m (leq-pred m n h) i p
  ... | inr (o , refl , p) =
    subst (Mem A) (sym (trans (cong ε (trans (cong (_+ o) (length-levels m)) (+-comm (m * 6) o))) (ε-at m o)))
          (blockMem m h o p)

  sat : ∀ i {A} → lookup (ctx t) i ≡ just A → Mem A (ε i)
  sat i e with lookup-split (levels t n) (tyB t n ∷ []) i e
  ... | inl p                    = levelsMem n (leq-refl″ n) i p
  ... | inr (zero , refl , refl) =
    subst (Mem (tyB t n)) (sym (trans (cong ε (trans (cong (_+ 0) (length-levels n)) (+-comm (n * 6) 0))) εball))
          (MemB false n)
  ... | inr (suc o , _ , ())

  ----------------------------------------------------------------------
  -- A derivable reverse goal is a reverse cell

  reverse-cell : ∀ s → infer (ctx t) s ≡ just (hom dir g (tyU t k) (var (uP k)) (var (uM k))) →
                 CellAt (suc k) g (H ρ) (val ⟦ s ⟧) ×
                 (pc (val ⟦ s ⟧) g (δ false k) ≈ uv true k) × (pc (val ⟦ s ⟧) g (δ true k) ≈ uv false k)
  reverse-cell s e =
    unfix (tyU t k) (dimU t k) (baseU t k) (cell m) ,
    ≈-trans (≈-sym (dfix (val ⟦ s ⟧) false (tyU t k) (dimU t k))) (≈-trans (fS m) (≡→≈ (cong val (εuP k)))) ,
    ≈-trans (≈-sym (dfix (val ⟦ s ⟧) true (tyU t k) (dimU t k)))
            (≈-trans (fT m) (≡→≈ (cong val (εuM k (leq-refl″ k)))))
    where
    m = soundness 𝔐 ε (ctx t) sat s e
    unfix : ∀ A {j M x} → dim A ≡ j → baseM A ≡ M → CellAt (suc (dim A)) g (baseM A) x → CellAt (suc j) g M x
    unfix A refl refl c = c

