------------------------------------------------------------------------
-- The composite of a pasting context exists (ledger item A3a, general
-- case).
--
-- If λ gives every variable of a pasting context Γ a cell of 𝒞 with
-- the boundary its type prescribes, the tree of Γ relabelled by λ has a
-- composite (`comp-ex`). By induction on the ps-derivation: the pair
-- y : A, f : x → y inserts the branch (f, y) at the end of the
-- rightmost node at height dim A, which ends with x (CaTTExp.Strict.
-- PsTree.tr-rm); the new composite is the old one with f composed on
-- at that node (`ins-cp`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Strict.Omega

module CaTTExp.Strict.PsComposite
  (𝕊 : Signature) (𝒞 : ωCat) (Mk : Signature.K 𝕊 → ωCat.C 𝒞 → Set)
  (λ′ : Nat → ωCat.C 𝒞)
  where

open Signature 𝕊
open ωCat 𝒞
open Basics 𝒞
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.OmegaPasting 𝒞
open import CaTTExp.Strict.PsTree 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.Strict.PsFacts 𝕊 using (lookup-top; lookup-wk; lookup-wk₂; lookup-<; <-suc)
open import CaTTExp.Strict.OmegaFree 𝕊 𝒞 Mk λ′ using (Good; BdL)

private
  +-suc : ∀ d k → d + suc k ≡ suc (d + k)
  +-suc zero    k = refl
  +-suc (suc d) k = cong suc (+-suc d k)

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

  lastv-++1 : ∀ {A : Set} (s : A) br T y → lastv s (br ++B cons T y nil) ≡ y
  lastv-++1 s nil          T y = refl
  lastv-++1 s (cons U z r) T y = lastv-++1 z r T y

  lastv-insLast : ∀ {A : Set} n (y f s : A) br → lastv s (insLast n y f br) ≡ lastv s br
  lastv-insLast n y f s nil                       = refl
  lastv-insLast n y f s (cons T z nil)            = refl
  lastv-insLast n y f s (cons T z (cons T′ z′ r)) = lastv-insLast n y f z (cons T′ z′ r)

------------------------------------------------------------------------
-- Relabelling commutes with insertion and the rightmost path.

mutual
  map-insert : ∀ {A B : Set} (g : A → B) n y f T → mapLT g (insert n y f T) ≡ insert n (g y) (g f) (mapLT g T)
  map-insert g zero    y f (node s br) = cong (node (g s)) (map-++ g br (cons (node f nil) y nil))
  map-insert g (suc n) y f (node s br) = cong (node (g s)) (map-insLast g n y f br)

  map-insLast : ∀ {A B : Set} (g : A → B) n y f br → mapB g (insLast n y f br) ≡ insLast n (g y) (g f) (mapB g br)
  map-insLast g n y f nil                       = refl
  map-insLast g n y f (cons T z nil)            = cong (λ U → cons U (g z) nil) (map-insert g n y f T)
  map-insLast g n y f (cons T z (cons T′ z′ r)) = cong (cons (mapLT g T) (g z)) (map-insLast g n y f (cons T′ z′ r))

mutual
  rm-map : ∀ {A B : Set} (g : A → B) n T x → RM n T x → RM n (mapLT g T) (g x)
  rm-map g zero    (node s br) x p = trans (sym (map-lastv g s br)) (cong g p)
  rm-map g (suc n) (node s br) x p = rmB-map g n br x p

  rmB-map : ∀ {A B : Set} (g : A → B) n br x → RMB n br x → RMB n (mapB g br) (g x)
  rmB-map g n nil                       x ()
  rmB-map g n (cons T z nil)            x p = rm-map g n T x p
  rmB-map g n (cons T z (cons T′ z′ r)) x p = rmB-map g n (cons T′ z′ r) x p

------------------------------------------------------------------------
-- Inserting a cell keeps the composite defined.

private
  root-src : ∀ {k T a} → Cp k T a → src k a ≡ rootLT T
  root-src (cp u) = cpB-src u

  last-tgt : ∀ {k x r a} → Cp k (node x r) a → tgt k a ≡ lastv x r
  last-tgt (cp u) = cpB-tgt u

  root-insert : ∀ {A : Set} n (y f : A) T → rootLT (insert n y f T) ≡ rootLT T
  root-insert zero    y f (node s br) = refl
  root-insert (suc n) y f (node s br) = refl

src-same : ∀ n k {T a a′ F Y} → Cp (suc k) T a → Cp (suc k) (insert n Y F T) a′ → src k a′ ≡ src k a
src-same n k {T} {a} {a′} {F} {Y} ca ca′ =
  trans (sym (src-src-< a′ (≤-refl (suc k))))
    (trans (cong (src k) (trans (root-src ca′) (trans (root-insert n Y F T) (sym (root-src ca)))))
           (src-src-< a (≤-refl (suc k))))

tgt-same : ∀ n k {T a a′ X F Y} → Cp (suc k) T a → Cp (suc k) (insert n Y F T) a′ → RM n T X →
           src (suc (n + k)) F ≡ X → tgt (suc (n + k)) F ≡ Y → tgt k a′ ≡ tgt k a
tgt-same zero k {node r brT} {a} {a′} {X} {F} {Y} ca ca′ rm sF tF =
  trans (sym (tgt-tgt-< a′ (≤-refl (suc k))))
    (trans (cong (tgt k) (trans (last-tgt ca′) (lastv-++1 r brT (node F nil) Y)))
      (trans (cong (tgt k) (sym tF))
        (trans (tgt-tgt-< F (≤-refl (suc k)))
          (trans (sym (tgt-src-< F (≤-refl (suc k))))
            (trans (cong (tgt k) (trans sF (sym (trans (last-tgt ca) rm))))
              (tgt-tgt-< a (≤-refl (suc k))))))))
tgt-same (suc n) k {node r brT} {a} {a′} {F = F} {Y} ca ca′ rm sF tF =
  trans (sym (tgt-tgt-< a′ (≤-refl (suc k))))
    (trans (cong (tgt k) (trans (last-tgt ca′) (lastv-insLast n Y F r brT)))
      (trans (cong (tgt k) (sym (last-tgt ca))) (tgt-tgt-< a (≤-refl (suc k)))))

mutual
  ins-cp : ∀ n k {T c X F Y} → Cp k T c → RM n T X →
           Dim≤ (suc (n + k)) F → src (n + k) F ≡ X → tgt (n + k) F ≡ Y → Dim≤ (n + k) Y →
           Σ C λ c′ → Cp k (insert n Y F T) c′
  ins-cp zero k {node s br} {c} {X} {F} {Y} (cp u) rm dF sF tF dY =
    _ , cp (cat k u v rm p₂)
    where
    p₁ : tgt k F ≡ src k Y
    p₁ = trans tF (sym dY)
    v : CpB k X (cons (node F nil) Y nil) (comp k F Y p₁)
    v = ccons (cp (cnil dF)) sF (cnil dY) p₁
    p₂ : tgt k c ≡ src k (comp k F Y p₁)
    p₂ = trans (cpB-tgt u) (trans rm (sym (cpB-src v)))
  ins-cp (suc n) k {node s br} (cp u) rm dF sF tF dY =
    let (c′ , u′) = ins-cpB n k u rm dF sF tF dY in c′ , cp u′

  ins-cpB : ∀ n k {s br c X F Y} → CpB k s br c → RMB n br X →
            Dim≤ (suc (suc (n + k))) F → src (suc (n + k)) F ≡ X → tgt (suc (n + k)) F ≡ Y →
            Dim≤ (suc (n + k)) Y → Σ C λ c′ → CpB k s (insLast n Y F br) c′
  ins-cpB n k (cnil _) () dF sF tF dY
  ins-cpB n k {s} {cons T z nil} {X = X} {F} {Y} (ccons {a = a} {b = b} ca e cb p) rm dF sF tF dY =
    let ix = sym (+-suc n k)
        (a′ , ca′) = ins-cp n (suc k) ca rm
                       (subst (λ m → Dim≤ (suc m) F) ix dF) (subst (λ m → src m F ≡ X) ix sF)
                       (subst (λ m → tgt m F ≡ Y) ix tF) (subst (λ m → Dim≤ m Y) ix dY)
        et = tgt-same n k ca ca′ rm sF tF
    in comp k a′ b (trans et p) , ccons ca′ (trans (src-same n k ca ca′) e) cb (trans et p)
  ins-cpB n k {s} {cons T z (cons T′ z′ r)} (ccons {a = a} ca e cb p) rm dF sF tF dY =
    let (b′ , cb′) = ins-cpB n k cb rm dF sF tF dY
    in comp k a b′ (trans p (trans (cpB-src cb) (sym (cpB-src cb′)))) ,
       ccons ca e cb′ (trans p (trans (cpB-src cb) (sym (cpB-src cb′))))

------------------------------------------------------------------------
-- The composite of the tree of a pasting context.

private
  ==-r : ∀ n → (n ==ℕ n) ≡ true
  ==-r zero    = refl
  ==-r (suc n) = ==-r n

  n<s : ∀ n → T (n <ℕ suc n)
  n<s zero    = tt
  n<s (suc n) = n<s n

  good-init : ∀ {Γ A B} → Good (Γ ▸ A ▸ B) → Good Γ
  good-init {Γ} {A} {B} g v C p = g v C (trans (lookup-wk₂ Γ A B v (lookup-< Γ v p)) p)

  lk-f : ∀ Γ A B → lookup (Γ ▸ A ▸ B) (suc (len Γ)) ≡ just B
  lk-f Γ A B = lookup-top (Γ ▸ A) B

  lk-y : ∀ Γ A B → lookup (Γ ▸ A ▸ B) (len Γ) ≡ just A
  lk-y Γ A B = trans (lookup-wk (Γ ▸ A) B (len Γ) (n<s (len Γ))) (lookup-top Γ A)

comp-ex : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Good Γ → Σ C λ c → Cp 0 (mapLT λ′ (tr Γ)) c
comp-ex pss g = λ′ 0 , cp (cnil (fst (g 0 ⋆ refl)))
comp-ex (pse {Γ} {x} {A} d) g =
  let (c , cc) = comp-ex d (good-init g)
      B = arr A (var x) (var (len Γ))
      (dF , sF , tF) = g (suc (len Γ)) B (lk-f Γ A B)
      dY = fst (g (len Γ) A (lk-y Γ A B))
      ix = sym (+-zero (dim A))
      rm = rm-map λ′ (dim A) (tr Γ) x (rmt-top (tr Γ) x A (tr-rm d))
      (c′ , cc′) = ins-cp (dim A) 0 cc rm
                     (subst (λ m → Dim≤ (suc m) (λ′ (suc (len Γ)))) ix dF)
                     (subst (λ m → src m (λ′ (suc (len Γ))) ≡ λ′ x) ix sF)
                     (subst (λ m → tgt m (λ′ (suc (len Γ))) ≡ λ′ (len Γ)) ix tF)
                     (subst (λ m → Dim≤ m (λ′ (len Γ))) ix dY)
  in c′ , subst (λ U → Cp 0 U c′) (sym (map-insert λ′ (dim A) (len Γ) (suc (len Γ)) (tr Γ))) cc′
comp-ex (psd d) g = comp-ex d g
