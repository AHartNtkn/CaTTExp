------------------------------------------------------------------------
-- Soundness of two-tier L in its strict model.
--
-- Every derivable term t : A over a pasting context Γ is a cell of
-- ν(K(Γ)), the free strict Gray-enriched category on Γ (hom by hom, the
-- strict ω-category of the Steiner complex λΘᵢ₊₁ ⊗ … ⊗ λΘⱼ):
--
--     sound-tm : PsInv Γ → Γ ⊢tm t ∶ A → IsCellTm Γ t A
--
-- where a coh is interpreted as the image, under the chain map of its
-- substitution, of
--   * the total cell T of its pasting context (operation case), or
--   * the identity on its source (coherence case).
-- This is Theorem 1(1) of notes/pseudo-vs-gray.md §3.6.
--
-- Two facts about Steiner complexes are taken as explicit module
-- parameters, not postulated:
--
--  (T-cell) the table T of the Gray tensor ⟨Θ₁⟩ ⊗ … ⊗ ⟨Θₙ⟩ of the
--      composites of the pasting diagrams, as computed by
--      CaTTExp.Gray.Support's chainT, is a cell of ν(K(Θ)) between the
--      first and last object. (Ara–Maltsiniotis, arXiv 1607.00668,
--      §A.16 and Prop. 4.13; Steiner 2004.)
--  (B-supp) "support determines the cell": two cells of ν(K(Θ)) of the
--      same dimension in the same hom whose downward-closed supports
--      (CaTTExp.Gray.Support's `down`) agree are equal. (Hadzihasanovic,
--      arXiv 2404.07273, Prop. 8.3.17 and Thm 11.2.18, for these
--      complexes; notes/conjectures/steiner-support-determines-cells.md
--      proves it for every Steiner complex.)
-- CaTTExp.Strict.CheckCells checks (T-cell) by evaluation on 18 shapes.
------------------------------------------------------------------------
module CaTTExp.Strict.Soundness where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.Subst
open import CaTTExp.Strict.L
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Subst ∅ graySide as S

------------------------------------------------------------------------
-- Finite sets via CaTTExp.Gray.Support's memT.

SetEq : TSet → TSet → Set
SetEq X Y = ∀ a → memT a X ≡ memT a Y

private
  ∨-assoc : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

  ∨-false : ∀ a → a ∨ false ≡ a
  ∨-false true  = refl
  ∨-false false = refl

  bool-flat : ∀ s y u t → (s ∨ y) ∨ ((u ∨ y) ∨ t) ≡ t ∨ (y ∨ (s ∨ u))
  bool-flat true true true true = refl
  bool-flat true true true false = refl
  bool-flat true true false true = refl
  bool-flat true true false false = refl
  bool-flat true false true true = refl
  bool-flat true false true false = refl
  bool-flat true false false true = refl
  bool-flat true false false false = refl
  bool-flat false true true true = refl
  bool-flat false true true false = refl
  bool-flat false true false true = refl
  bool-flat false true false false = refl
  bool-flat false false true true = refl
  bool-flat false false true false = refl
  bool-flat false false false true = refl
  bool-flat false false false false = refl

  bool-tw : ∀ l f t c → (l ∨ f) ∨ ((l ∨ t) ∨ c) ≡ (l ∨ (f ∨ t)) ∨ c
  bool-tw true true true true = refl
  bool-tw true true true false = refl
  bool-tw true true false true = refl
  bool-tw true true false false = refl
  bool-tw true false true true = refl
  bool-tw true false true false = refl
  bool-tw true false false true = refl
  bool-tw true false false false = refl
  bool-tw false true true true = refl
  bool-tw false true true false = refl
  bool-tw false true false true = refl
  bool-tw false true false false = refl
  bool-tw false false true true = refl
  bool-tw false false true false = refl
  bool-tw false false false true = refl
  bool-tw false false false false = refl

memT-++ : ∀ a X Y → memT a (X ++ Y) ≡ memT a X ∨ memT a Y
memT-++ a []      Y = refl
memT-++ a (x ∷ X) Y = trans (cong ((a ==T x) ∨_) (memT-++ a X Y)) (sym (∨-assoc (a ==T x) (memT a X) (memT a Y)))

==T-sound : ∀ a b → T (a ==T b) → a ≡ b
==T-sound []       []       _ = refl
==T-sound (x ∷ xs) (y ∷ ys) p =
  cong₂ _∷_ (==ℕ-sound x y (∧-fst p)) (==T-sound xs ys (∧-snd {x ==ℕ y} p))

==T-refl : ∀ a → T (a ==T a)
==T-refl []       = tt
==T-refl (x ∷ xs) = T-∧ (==ℕ-refl x) (==T-refl xs)
  where
  T-∧ : ∀ {a b} → T a → T b → T (a ∧ b)
  T-∧ {true} _ q = q

private
  T-∧ : ∀ {a b} → T a → T b → T (a ∧ b)
  T-∧ {true} _ q = q

  T-∨r : ∀ a {b} → T b → T (a ∨ b)
  T-∨r true  _ = tt
  T-∨r false q = q

⊆T-sound : ∀ xs ys → T (⊆T xs ys) → ∀ a → T (memT a xs) → T (memT a ys)
⊆T-sound (x ∷ xs) ys p a m with a ==T x in e
... | true  = subst (λ z → T (memT z ys)) (sym (==T-sound a x (subst T (sym e) tt))) (∧-fst p)
... | false = ⊆T-sound xs ys (∧-snd {memT x ys} p) a m

⊆T-complete : ∀ xs ys → (∀ a → T (memT a xs) → T (memT a ys)) → T (⊆T xs ys)
⊆T-complete []       ys f = tt
⊆T-complete (x ∷ xs) ys f =
  T-∧ (f x (subst (λ b → T (b ∨ memT x xs)) (sym (T→≡ (==T-refl x))) tt))
      (⊆T-complete xs ys (λ a m → f a (T-∨r (a ==T x) m)))
  where
  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

≈T-via : ∀ A B F → T (≈T A F) → T (≈T B F) → T (≈T A B)
≈T-via A B F p q =
  T-∧ (⊆T-complete A B (λ a m → ⊆T-sound F B (∧-snd {⊆T B F} q) a (⊆T-sound A F (∧-fst p) a m)))
      (⊆T-complete B A (λ a m → ⊆T-sound F A (∧-snd {⊆T A F} p) a (⊆T-sound B F (∧-fst q) a m)))

------------------------------------------------------------------------
-- The flattened table of t : A is its support (CaTTExp.Gray.Support's
-- supp t A), as a set.

flat-supp : ∀ t A s u → SetEq (flat (towerOf t (arr A s u))) (supp t (arr A s u))
flat-supp t ⋆ s u a = sym (trans (memT-++ a (topS t) []) (∨-false (memT a (topS t))))
flat-supp t (arr B a' b') s u a =
  trans (memT-++ a (flat (towerOf s A')) _)
 (trans (cong₂ _∨_ (flat-supp s B a' b' a) (memT-++ a (flat (towerOf u A')) (topS t)))
 (trans (cong₂ (λ X Y → X ∨ (Y ∨ memT a (topS t)))
          (memT-++ a (topS s) (suppTy A')) (trans (flat-supp u B a' b' a) (memT-++ a (topS u) (suppTy A'))))
 (trans (bool-flat (memT a (topS s)) (memT a (suppTy A')) (memT a (topS u)) (memT a (topS t)))
        (sym (trans (memT-++ a (topS t) _)
              (cong (memT a (topS t) ∨_)
                (trans (memT-++ a (suppTy A') _) (cong (memT a (suppTy A') ∨_) (memT-++ a (topS s) (topS u))))))))))
  where
  A' = arr B a' b'

------------------------------------------------------------------------
-- The total cell T and its boundaries, as towers.

twT : List Hom → Bool → Nat → Tower
twT hs sg zero    = base (chainT sg zero hs)
twT hs sg (suc m) = step (twT hs false m) (twT hs true m) (chainT sg (suc m) hs)

flat-twT : ∀ hs sg m → SetEq (flat (twT hs sg m)) (lowerT m hs ++ chainT sg m hs)
flat-twT hs sg zero    a = refl
flat-twT hs sg (suc m) a =
  trans (memT-++ a (flat (twT hs false m)) _)
 (trans (cong₂ _∨_ (trans (flat-twT hs false m a) (memT-++ a (lowerT m hs) _))
                   (trans (memT-++ a (flat (twT hs true m)) _)
                          (cong (_∨ memT a (chainT sg (suc m) hs))
                                (trans (flat-twT hs true m a) (memT-++ a (lowerT m hs) _)))))
 (trans (bool-tw (memT a (lowerT m hs)) (memT a (chainT false m hs)) (memT a (chainT true m hs))
                 (memT a (chainT sg (suc m) hs)))
        (sym (trans (memT-++ a (lowerT (suc m) hs) _)
              (cong (_∨ memT a (chainT sg (suc m) hs))
                (trans (memT-++ a (lowerT m hs) _)
                       (cong (memT a (lowerT m hs) ∨_) (memT-++ a (chainT false m hs) (chainT true m hs)))))))))

------------------------------------------------------------------------
-- Endpoints.

endsV→endsTy : ∀ A {x y} → endsV A ≡ just (x , y) → endsTy A ≡ just (var x , var y)
endsV→endsTy ⋆ ()
endsV→endsTy (arr ⋆ (var x) (var y)) refl = refl
endsV→endsTy (arr ⋆ (var x) (coh _ _ _)) ()
endsV→endsTy (arr ⋆ (var x) (cst ()))
endsV→endsTy (arr ⋆ (coh _ _ _) _) ()
endsV→endsTy (arr ⋆ (cst ()) _)
endsV→endsTy (arr (arr B s t) _ _) e = endsV→endsTy (arr B s t) e

------------------------------------------------------------------------
-- The theorem.

closed : S.Closed
closed ()

-- The two hypotheses, named so that every module using them states the
-- same thing.
TCell : Set
TCell = ∀ {Θ} → Θ ⊢ps → ∀ A x y → T (endsOK Θ A) → endsTy A ≡ just (var x , var y) →
        IsCellL Θ x y (dimK (homs Θ)) (twT (homs Θ) true (dimK (homs Θ)))

-- Two cells in the same hom x → y.
BSupp : Set
BSupp = ∀ {Θ} → Θ ⊢ps → ∀ x y n X Y L M →
        IsCellL Θ x y n X → IsCellL Θ x y n Y →
        SetEq (flat X) L → SetEq (flat Y) M → T (≈T (down Θ L) (down Θ M)) → X ≈w Y

module Soundness (T-cell : TCell) (B-supp : BSupp) where

  -- Composites of 1-cells (the coh's type is a 1-cell type).
  sound-op⋆ : ∀ {Γ Δ t u σ} → Δ ⊢ps → T (graySide Δ ⋆ t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
              IsCellTm Δ t ⋆ → IsCellTm Δ u ⋆ →
              IsCellTm Γ (coh Δ (arr ⋆ t u) σ) (arr ⋆ t u [ σ ]ty)
  sound-op⋆ {Γ} {Δ} {σ = σ} psΔ ok sσ cellσ (i , refl , li) (j , refl , lj) =
    let (i' , σi , li') = cellσ i ⋆ li
        (j' , σj , lj') = cellσ j ⋆ lj
        d0 : dimK hs ≡ 0
        d0 = ==ℕ-sound (dimK hs) 0 (∧-fst ok)
        cT = T-cell psΔ (arr ⋆ (var i) (var j)) i j (∧-snd {dimK hs ==ℕ 0} ok) refl
        tr = SM.transport-σ i j i' j' (dimK hs) (twT hs true (dimK hs)) σi σj cT
        tr0 = subst (λ m → IsCellL Γ i' j' m (mapTw (applyF (topsSub σ)) (twT hs true m))) d0 tr
    in (i' , j') , ends-sub→ (arr ⋆ (var i) (var j)) σ refl σi σj , li' , lj' ,
       subst (λ m → IsCellL Γ i' j' 0 (base (applyF (topsSub σ) (chainT true m hs)))) (sym d0) tr0
    where
    hs = homs Δ
    module SM = SubstMap cellσ (snd (S.sub-sc closed sσ)) (psInv psΔ)

  sound-arr : ∀ {Γ Δ t u σ} → ∀ A₀ a₀ b₀ → Δ ⊢ps →
              T (graySide Δ (arr A₀ a₀ b₀) t u) → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ →
              Δ ⊢tm t ∶ arr A₀ a₀ b₀ → Δ ⊢tm u ∶ arr A₀ a₀ b₀ →
              IsCellTm Δ t (arr A₀ a₀ b₀) → IsCellTm Δ u (arr A₀ a₀ b₀) →
              IsCellTm Γ (coh Δ (arr (arr A₀ a₀ b₀) t u) σ) (arr (arr A₀ a₀ b₀) t u [ σ ]ty)
  sound-arr {Γ} {Δ} {t} {u} {σ} A₀ a₀ b₀ psΔ ok sσ cellσ d e
            ((e₁ , e₂) , ee , l₁ , l₂ , cT) ((e₁' , e₂') , ee' , _ , _ , cU') =
    let (x' , σx , lx') = cellσ e₁ ⋆ l₁
        (y' , σy , ly') = cellσ e₂ ⋆ l₂
        trΓ = SM.transport-σ e₁ e₂ x' y' (dim A) (X₀ (cohCase Δ A t u)) σx σy
                (cellX (cohCase Δ A t u) refl)
        G   = towerOf (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
        Geq : mapTw (applyF (topsSub σ)) (X₀ (cohCase Δ A t u)) ≈w G
        Geq = ≈w-sym (towerOf (t [ σ ]tm) (A [ σ ]ty)) _ (tower-sub t A σ sct scA) ,
              ≈w-sym (towerOf (u [ σ ]tm) (A [ σ ]ty)) _ (tower-sub u A σ scu scA) ,
              ≈-refl
    in (x' , y') , ends-sub→ A σ ee σx σy , lx' , ly' ,
       subst (λ m → IsCellL Γ x' y' m G) (sym (dim-sub A σ))
         (Cells.IsCell-≈ (∂T Γ) (Basis Γ x' y') (dim A) _ G Geq trΓ)
    where
    A = arr A₀ a₀ b₀
    hs = homs Δ
    n = dim A₀
    lenσ = snd (S.sub-sc closed sσ)
    module SM = SubstMap cellσ lenσ (psInv psΔ)
    sct : S.ScTm (lenₛ σ) t
    sct = subst (λ m → S.ScTm m t) (sym lenσ) (S.tm-sc closed d)
    scA : S.ScTy (lenₛ σ) A
    scA = subst (λ m → S.ScTy m A) (sym lenσ) (S.tm-ty-sc closed d)
    scu : S.ScTm (lenₛ σ) u
    scu = subst (λ m → S.ScTm m u) (sym lenσ) (S.tm-sc closed e)
    cU : IsCellL Δ e₁ e₂ n (towerOf u A)
    cU = subst (λ e' → IsCellL Δ (fst e') (snd e') n (towerOf u A)) (just-inj (trans (sym ee') ee)) cU'
    X₀ : Bool → Tower
    X₀ b = step (towerOf t A) (towerOf u A) (if b then [] else topT hs)
    opcell : ∀ m → suc n ≡ m → IsCellL Δ e₁ e₂ m (twT hs true m) →
             T (≈T (down Δ (supp t A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT false (m ∸ 1) hs))) →
             T (≈T (down Δ (supp u A)) (down Δ (lowerT (m ∸ 1) hs ++ chainT true (m ∸ 1) hs))) →
             ∀ C → C ≡ chainT true m hs → IsCellL Δ e₁ e₂ (suc n) (step (towerOf t A) (towerOf u A) C)
    opcell .(suc n) refl cTT pt pu C refl =
      let c₋ = fst cTT
          c₊ = fst (snd cTT)
          et = B-supp psΔ e₁ e₂ n (towerOf t A) (twT hs false n) (supp t A) (lowerT n hs ++ chainT false n hs) cT c₋
                 (flat-supp t A₀ a₀ b₀) (flat-twT hs false n) pt
          eu = B-supp psΔ e₁ e₂ n (towerOf u A) (twT hs true n) (supp u A) (lowerT n hs ++ chainT true n hs) cU c₊
                 (flat-supp u A₀ a₀ b₀) (flat-twT hs true n) pu
      in Cells.IsCell-≈ (∂T Δ) (Basis Δ e₁ e₂) (suc n) (twT hs true (suc n)) _
           (≈w-sym (towerOf t A) _ et , ≈w-sym (towerOf u A) _ eu , ≈-refl) cTT
    cellX : ∀ b → cohCase Δ A t u ≡ b → IsCellL Δ e₁ e₂ (dim A) (X₀ b)
    cellX true ec =
      let cc = subst T (sym ec) tt
          pt = ∧-fst (∧-snd {endsOK Δ A} cc)
          pu = ∧-snd {≈T (down Δ (supp t A)) (down Δ (fullT hs))} (∧-snd {endsOK Δ A} cc)
          eTU = B-supp psΔ e₁ e₂ n (towerOf t A) (towerOf u A) (supp t A) (supp u A) cT cU
                  (flat-supp t A₀ a₀ b₀) (flat-supp u A₀ a₀ b₀)
                  (≈T-via (down Δ (supp t A)) (down Δ (supp u A)) (down Δ (fullT hs)) pt pu)
      in cT , cU , Par-same t u A₀ a₀ b₀ ,
         ≈w-top (towerOf t A) (towerOf u A) eTU , tt
    cellX false ec =
      let oc = subst (λ b → T (b ∨ opCase Δ A t u)) ec ok
          okE = ∧-fst oc
          dA  = ==ℕ-sound (dim A) (dimK hs) (∧-fst (∧-snd {endsOK Δ A} oc))
          rest = ∧-snd {dim A ==ℕ dimK hs} (∧-snd {endsOK Δ A} oc)
          pt = ∧-fst rest
          pu = ∧-snd {≈T (down Δ (supp t A)) (down Δ (bdryT false hs))} rest
      in opcell (dimK hs) dA (T-cell psΔ A e₁ e₂ okE (endsV→endsTy A ee)) pt pu (topT hs) refl

  mutual
    sound-tm : ∀ {Γ t A} → PsInv Γ → Γ ⊢tm t ∶ A → IsCellTm Γ t A
    sound-tm inv (var-wf _ eq) = var-cell inv _ _ eq
    sound-tm inv (coh-wf {A = A} psΔ ctxΔ tyΔ ok sσ) = sound-coh inv A psΔ ctxΔ tyΔ ok sσ
    sound-tm inv (cst-wf {()} _ _)

    sound-ty : ∀ {Γ A t u} → PsInv Γ → Γ ⊢ty arr A t u → IsCellTm Γ t A × IsCellTm Γ u A
    sound-ty inv (arr-wf d e) = sound-tm inv d , sound-tm inv e

    sound-sub : ∀ {Γ σ Δ} → PsInv Γ → Δ ⊢ctx → Γ ⊢sub σ ∶ Δ → Cellular Γ σ Δ
    sound-sub inv ε-wf (⟨⟩-wf _) v B ()
    sound-sub {Γ} inv (▸-wf {Δ} {A} w a) (,-wf {σ} {_} {t} sσ d) v B eq with S.sub-sc closed sσ
    ... | (_ , l) with v ==ℕ len Δ in e
    ...   | true rewrite l | e =
      subst (λ X → IsCellTm Γ t (X [ σ ,ₛ t ]ty)) (just-inj eq)
        (subst (IsCellTm Γ t)
          (sym (S.ext-ty A σ t (subst (λ n → S.ScTy n A) (sym l) (S.ty-sc closed a))))
          (sound-tm inv d))
    ...   | false rewrite l | e =
      subst (IsCellTm Γ (lookupₛ σ v))
        (sym (S.ext-ty B σ t (subst (λ n → S.ScTy n B) (sym l) (snd (S.ctx-lookup closed w eq)))))
        (sound-sub inv w sσ v B eq)

    sound-coh : ∀ {Γ Δ t u σ} → PsInv Γ → ∀ A → Δ ⊢ps → Δ ⊢ctx → Δ ⊢ty arr A t u →
                T (graySide Δ A t u) → Γ ⊢sub σ ∶ Δ →
                IsCellTm Γ (coh Δ (arr A t u) σ) (arr A t u [ σ ]ty)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv ⋆ psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-op⋆ psΔ ok sσ (sound-sub inv ctxΔ sσ) (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)
    sound-coh {Γ} {Δ} {t} {u} {σ} inv (arr A₀ a₀ b₀) psΔ ctxΔ (arr-wf d e) ok sσ =
      sound-arr A₀ a₀ b₀ psΔ ok sσ (sound-sub inv ctxΔ sσ) d e
        (sound-tm (psInv psΔ) d) (sound-tm (psInv psΔ) e)

