------------------------------------------------------------------------
-- D13 for every dimension: the explicit disk cylinder types T_m of
-- CaTTExp.GrayCtx.NaturalExplicit are well typed for every m, so the
-- cylinders Γ ⊗ D¹ and D¹ ⊗ Γ are well formed for every well-formed
-- globular Γ.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.NaturalAll where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left; odd)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalWF
open import CaTTExp.GrayCtx.NaturalExplicit
open import CaTTExp.Derived using (nB; BK; wK; LK; lK; subst₂; tm-ty; sphSub; lenₛ-sph; Sph; Dsk; dsk-ps; ps-wf)
open import CaTTExp.DerivedBoundary
  using (σR; rwT; tyK; tgtK; srcK; rwT-wf; rwT-ty0; rwT-ty; hL; σL; lwT; lwT-wf; lwT-ty; lwT-ty0;
         C-sph; arr-inj₁; arr-inj₃; tyK-arr; srcK-arr; tgtK-arr; σLp; sc-aL-in)

------------------------------------------------------------------------
-- Arithmetic.

∸-self : ∀ n → n ∸ n ≡ 0
∸-self zero    = refl
∸-self (suc n) = ∸-self n

+-zero : ∀ n → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

nB-split : ∀ k n → T (k <ℕ n) → n ≡ nB k (n ∸ suc k)
nB-split zero    (suc n) _ = cong suc (sym (+-zero n))
nB-split (suc k) (suc n) p = trans (cong suc (nB-split k n p)) (cong suc (sym (+-suc (n ∸ suc k) k)))

∸-step : ∀ k n → T (k <ℕ n) → n ∸ k ≡ suc (n ∸ suc k)
∸-step zero    (suc n) _ = refl
∸-step (suc k) (suc n) p = ∸-step k n p

==-false : ∀ a b → T (a <ℕ b) → (b ==ℕ a) ≡ false
==-false zero    (suc b) _ = refl
==-false (suc a) (suc b) p = ==-false a b p

arr-inj₂ : ∀ {A B s t u v} → arr A s t ≡ arr B u v → s ≡ u
arr-inj₂ refl = refl

arr≡ : ∀ {A B s t u v} → A ≡ B → s ≡ u → t ≡ v → arr A s t ≡ arr B u v
arr≡ refl refl refl = refl

------------------------------------------------------------------------
-- Typing the smart whiskerings of NaturalExplicit.G.

module WL (sd : Side) (Γ : Ctx) (N : Nat) where
  open G sd Γ N

  tyE-sound : ∀ {u A} → Γ ⊢tm u ∶ A → tyE u ≡ A
  tyE-sound (var-wf {i} _ eq)  = lookup-tyAt Γ i eq
  tyE-sound (coh-wf _ _ _ _ _) = refl
  tyE-sound (cst-wf {k} _ _)   = ⊥-elim k

  rwE≡ : ∀ {c h C H} → tyE c ≡ C → tyE h ≡ H →
         rwE c h ≡ coh (BK (pred (dim H)) (dim C ∸ suc (pred (dim H))))
                       (wK (pred (dim H)) (dim C ∸ suc (pred (dim H)))) (σR c C (tgtTm H) h)
  rwE≡ refl refl = refl

  lwE≡ : ∀ {h c C H} → tyE c ≡ C → tyE h ≡ H →
         lwE h c ≡ coh (LK (pred (dim H)) (dim C ∸ suc (pred (dim H))))
                       (lK (pred (dim H)) (dim C ∸ suc (pred (dim H))))
                       (σL (pred (dim H)) (dim C ∸ suc (pred (dim H))) h (srcTm H) c C)
  lwE≡ refl refl = refl

  -- The composite c ;ₖ h of two (k+1)-cells.
  TR0 : ∀ {c h B s a z} → Γ ⊢tm c ∶ arr B s a → Γ ⊢tm h ∶ arr B a z → Γ ⊢tm rwE c h ∶ arr B s z
  TR0 {c} {h} {B} {s} {a} {z} dc dh =
    subst₂ (λ u X → Γ ⊢tm u ∶ X) (sym e1)
      (trans (rwT-ty0 k c C z h refl) (arr≡ (sym (arr-inj₁ eq)) (sym (arr-inj₂ eq)) refl))
      (rwT-wf k 0 dc refl dh')
    where
    k = dim B
    C = arr B s a
    eq : C ≡ arr (tyK k C) (srcK k C) (tgtK k C)
    eq = C-sph k C refl
    dh' : Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z
    dh' = subst₂ (λ X Y → Γ ⊢tm h ∶ arr X Y z) (arr-inj₁ eq) (arr-inj₃ eq) dh
    e1 : rwE c h ≡ rwT k 0 c C z h
    e1 = trans (rwE≡ (tyE-sound dc) (tyE-sound dh))
               (cong (λ j → coh (BK k j) (wK k j) (σR c C z h)) (∸-self k))

  -- c ▹ₖ h for dim c > k + 1, by its boundary.
  TR+ : ∀ {c h C' s t B a z} → Γ ⊢tm c ∶ arr C' s t → Γ ⊢tm h ∶ arr B a z → T (dim B <ℕ dim C') →
        B ≡ tyK (dim B) (arr C' s t) → a ≡ tgtK (dim B) (arr C' s t) →
        Γ ⊢tm rwE c h ∶ arr (tyE (rwE s h)) (rwE s h) (rwE t h)
  TR+ {c} {h} {C'} {s} {t} {B} {a} {z} dc dh lt eB ea with tm-ty dc
  ... | arr-wf ds dt =
    subst₂ (λ u X → Γ ⊢tm u ∶ X) (sym e1)
      (trans (rwT-ty k j' c C' s t z h e') (sym (arr≡ (cong tyE es) es et)))
      (rwT-wf k (suc j') dc (cong suc e') dh')
    where
    k = dim B
    j' = dim C' ∸ suc k
    C = arr C' s t
    e' : dim C' ≡ nB k j'
    e' = nB-split k (dim C') lt
    dh' : Γ ⊢tm h ∶ arr (tyK k C) (tgtK k C) z
    dh' = subst₂ (λ X Y → Γ ⊢tm h ∶ arr X Y z) eB ea dh
    e1 : rwE c h ≡ rwT k (suc j') c C z h
    e1 = trans (rwE≡ (tyE-sound dc) (tyE-sound dh))
               (cong (λ j → coh (BK k j) (wK k j) (σR c C z h)) (∸-step k (dim C') lt))
    es : rwE s h ≡ rwT k j' s C' z h
    es = rwE≡ (tyE-sound ds) (tyE-sound dh)
    et : rwE t h ≡ rwT k j' t C' z h
    et = rwE≡ (tyE-sound dt) (tyE-sound dh)

  -- The composite h ;ₖ c of two (k+1)-cells, as a left whiskering.
  TL0 : ∀ {c h B x a b} → Γ ⊢tm c ∶ arr B a b → Γ ⊢tm h ∶ arr B x a → Γ ⊢tm lwE h c ∶ arr B x b
  TL0 {c} {h} {B} {x} {a} {b} dc dh =
    subst₂ (λ u X → Γ ⊢tm u ∶ X) (sym e1)
      (trans (lwT-ty0 k h x c C refl) (arr≡ (sym (arr-inj₁ eq)) refl (sym (arr-inj₃ eq))))
      (lwT-wf k 0 dc refl dh')
    where
    k = dim B
    C = arr B a b
    eq : C ≡ arr (tyK k C) (srcK k C) (tgtK k C)
    eq = C-sph k C refl
    dh' : Γ ⊢tm h ∶ hL k x C
    dh' = subst₂ (λ X Y → Γ ⊢tm h ∶ arr X x Y) (arr-inj₁ eq) (arr-inj₂ eq) dh
    e1 : lwE h c ≡ lwT k 0 h x c C
    e1 = trans (lwE≡ (tyE-sound dc) (tyE-sound dh))
               (cong (λ j → coh (LK k j) (lK k j) (σL k j h x c C)) (∸-self k))

  -- h ◃ₖ c for dim c > k + 1, by its boundary.
  TL+ : ∀ {c h C' s t B x y} → Γ ⊢tm c ∶ arr C' s t → Γ ⊢tm h ∶ arr B x y → T (dim B <ℕ dim C') →
        B ≡ tyK (dim B) (arr C' s t) → y ≡ srcK (dim B) (arr C' s t) →
        Γ ⊢tm lwE h c ∶ arr (tyE (lwE h s)) (lwE h s) (lwE h t)
  TL+ {c} {h} {C'} {s} {t} {B} {x} {y} dc dh lt eB ey with tm-ty dc
  ... | arr-wf ds dt =
    subst₂ (λ u X → Γ ⊢tm u ∶ X) (sym e1)
      (trans (lwT-ty k j' h x c C' s t e') (sym (arr≡ (cong tyE es) es et)))
      (lwT-wf k (suc j') dc (cong suc e') dh')
    where
    k = dim B
    j' = dim C' ∸ suc k
    C = arr C' s t
    e' : dim C' ≡ nB k j'
    e' = nB-split k (dim C') lt
    dh' : Γ ⊢tm h ∶ hL k x C
    dh' = subst₂ (λ X Y → Γ ⊢tm h ∶ arr X x Y) eB ey dh
    e1 : lwE h c ≡ lwT k (suc j') h x c C
    e1 = trans (lwE≡ (tyE-sound dc) (tyE-sound dh))
               (cong (λ j → coh (LK k j) (lK k j) (σL k j h x c C)) (∸-step k (dim C') lt))
    es : lwE h s ≡ lwT k j' h x s C'
    es = lwE≡ (tyE-sound ds) (tyE-sound dh)
    et : lwE h t ≡ lwT k j' h x t C'
    et = lwE≡ (tyE-sound dt) (tyE-sound dh)

------------------------------------------------------------------------
-- The types of the whiskerings W_{e+1} c of a cell c of dimension k + e.

cons-L : ∀ sd e → cpy sd (srcW sd) (suc e) ≡ cpy sd L (suc (suc e))
cons-L right e = refl
cons-L left  e = refl

cons-R : ∀ sd e → cpy sd (tgtW sd) (suc e) ≡ cpy sd R (suc (suc e))
cons-R right e = refl
cons-R left  e = refl

module Lam (sd : Side) (Γ : Ctx) (N : Nat) where
  open G sd Γ N

  -- The type of the cells of dimension p in copy b.
  Aty : Bool → Nat → Ty
  Aty true  p = rnTy (N +_) (aL p)
  Aty false p = aL p

  mutual
    Λ : Which → Nat → Nat → Ty
    Λ w e zero    = base w e
    Λ w e (suc k) = arr (Λ w e k) (whiskE w (suc e) (cell b (dbl (k + e))))
                                  (whiskE w (suc e) (cell b (suc (dbl (k + e)))))
      where b = cpy sd w (suc e)

    base : Which → Nat → Ty
    base w zero    = ⋆
    base L (suc e) = arr (Λ (srcW sd) e 0)
                         (whiskE (srcW sd) (suc e) (cell (cpy sd L (suc (suc e))) (dbl e)))
                         (Tc e (suc (dbl e)))
    base R (suc e) = arr (Λ (tgtW sd) e 0)
                         (Sc e (dbl e))
                         (whiskE (tgtW sd) (suc e) (cell (cpy sd R (suc (suc e))) (suc (dbl e))))

  -- The type of the generator y ⊗ e, y of dimension q.
  Gq : Nat → Nat → Ty
  Gq q y = arr (Λ (srcW sd) q 0) (Sc q y) (Tc q y)

  Aty-0 : ∀ b → Aty b 0 ≡ ⋆
  Aty-0 true  = refl
  Aty-0 false = refl

  Aty-suc : ∀ b p → Aty b (suc p) ≡ arr (Aty b p) (cell b (dbl p)) (cell b (suc (dbl p)))
  Aty-suc true  p = refl
  Aty-suc false p = refl

  Λ0 : ∀ w k → Λ w 0 k ≡ Aty (cpy sd w 1) (k + 0)
  Λ0 w zero    = sym (Aty-0 (cpy sd w 1))
  Λ0 w (suc k) = trans (cong (λ X → arr X _ _) (Λ0 w k)) (sym (Aty-suc (cpy sd w 1) (k + 0)))

  -- The two whiskerings have the same type on cells of dimension e.
  E : ∀ e → base L e ≡ base R e
  E zero    = refl
  E (suc e) =
    arr≡ (E' (srcW sd) (tgtW sd) e)
         (cong (λ b → whiskE (srcW sd) (suc e) (cell b (dbl e))) (sym (cons-L sd e)))
         (cong (λ b → whiskE (tgtW sd) (suc e) (cell b (suc (dbl e)))) (cons-R sd e))
    where
    E' : ∀ w w' e → base w e ≡ base w' e
    E' L L e = refl
    E' L R e = E e
    E' R L e = sym (E e)
    E' R R e = refl

  E' : ∀ w w' e → Λ w e 0 ≡ Λ w' e 0
  E' L L e = refl
  E' L R e = E e
  E' R L e = sym (E e)
  E' R R e = refl

  mutual
    dim-Λ : ∀ w e k → dim (Λ w e k) ≡ k + e
    dim-Λ w e zero    = dim-base w e
    dim-Λ w e (suc k) = cong suc (dim-Λ w e k)

    dim-base : ∀ w e → dim (base w e) ≡ e
    dim-base w zero    = refl
    dim-base L (suc e) = cong suc (dim-Λ (srcW sd) e 0)
    dim-base R (suc e) = cong suc (dim-Λ (tgtW sd) e 0)

  e<sk+e : ∀ k e → T (e <ℕ suc (k + e))
  e<sk+e zero    e = n<sn e
  e<sk+e (suc k) e = <-trans e (suc (k + e)) (suc (suc (k + e))) (e<sk+e k e) (n<sn (suc (k + e)))

  -- The e-boundary of Λ w e (suc k).
  Λbd : ∀ w e k → (tyK e (Λ w e (suc k)) ≡ Λ w e 0) × ((srcK e (Λ w e (suc k)) ≡ whiskE w (suc e) (cell (cpy sd w (suc e)) (dbl e))) ×
                                                       (tgtK e (Λ w e (suc k)) ≡ whiskE w (suc e) (cell (cpy sd w (suc e)) (suc (dbl e)))))
  Λbd w e zero    =
    let eq = C-sph e (Λ w e 1) (cong suc (dim-Λ w e 0)) in
    sym (arr-inj₁ eq) , sym (arr-inj₂ eq) , sym (arr-inj₃ eq)
  Λbd w e (suc k) =
    let (a , b , c) = Λbd w e k in
    trans (tyK-arr e C' s t p) a , trans (srcK-arr e C' s t p) b , trans (tgtK-arr e C' s t p) c
    where
    C' = Λ w e (suc k)
    s = whiskE w (suc e) (cell (cpy sd w (suc e)) (dbl (suc k + e)))
    t = whiskE w (suc e) (cell (cpy sd w (suc e)) (suc (dbl (suc k + e))))
    p : T (e <ℕ dim C')
    p = subst (λ n → T (e <ℕ n)) (sym (dim-Λ w e (suc k))) (e<sk+e k e)

------------------------------------------------------------------------
-- The whiskerings are well typed, given the types of the cells and of
-- the generators below dimension m.

module Wh (sd : Side) (Γ : Ctx) (N m : Nat)
  (cellTy : ∀ b p → T (p <ℕ m) →
     (Γ ⊢tm G.cell sd Γ N b (dbl p) ∶ Lam.Aty sd Γ N b p) ×
     (Γ ⊢tm G.cell sd Γ N b (suc (dbl p)) ∶ Lam.Aty sd Γ N b p))
  (genTy : ∀ q → T (q <ℕ m) →
     (Γ ⊢tm G.gen sd Γ N (dbl q) ∶ Lam.Gq sd Γ N q (dbl q)) ×
     (Γ ⊢tm G.gen sd Γ N (suc (dbl q)) ∶ Lam.Gq sd Γ N q (suc (dbl q))))
  where
  open G sd Γ N
  open Lam sd Γ N
  open WL sd Γ N

  ks : ∀ k e → k + suc e ≡ suc (k + e)
  ks = +-suc

  e<m : ∀ k e → T (k + suc e <ℕ m) → T (e <ℕ m)
  e<m k e p = <-trans e (k + suc e) m (subst (λ n → T (e <ℕ n)) (sym (ks k e)) (e<sk+e k e)) p

  lt-Λ : ∀ w e k → T (dim (Λ w e 0) <ℕ dim (Λ w e (suc k)))
  lt-Λ w e k = subst₂ (λ a b → T (a <ℕ b)) (sym (dim-Λ w e 0)) (sym (dim-Λ w e (suc k))) (e<sk+e k e)

  ty≡ : ∀ w e k → Λ w e 0 ≡ tyK (dim (Λ w e 0)) (Λ w e (suc k))
  ty≡ w e k = subst (λ n → Λ w e 0 ≡ tyK n (Λ w e (suc k))) (sym (dim-Λ w e 0)) (sym (fst (Λbd w e k)))

  src≡ : ∀ w e k → whiskE w (suc e) (cell (cpy sd w (suc e)) (dbl e)) ≡ srcK (dim (Λ w e 0)) (Λ w e (suc k))
  src≡ w e k = subst (λ n → whiskE w (suc e) (cell (cpy sd w (suc e)) (dbl e)) ≡ srcK n (Λ w e (suc k))) (sym (dim-Λ w e 0)) (sym (fst (snd (Λbd w e k))))

  tgt≡ : ∀ w e k → whiskE w (suc e) (cell (cpy sd w (suc e)) (suc (dbl e))) ≡ tgtK (dim (Λ w e 0)) (Λ w e (suc k))
  tgt≡ w e k = subst (λ n → whiskE w (suc e) (cell (cpy sd w (suc e)) (suc (dbl e))) ≡ tgtK n (Λ w e (suc k))) (sym (dim-Λ w e 0)) (sym (snd (snd (Λbd w e k))))

  WTy : Nat → Set
  WTy e = ∀ k w c → T (k + e <ℕ suc m) → Γ ⊢tm c ∶ Aty (cpy sd w (suc e)) (k + e) →
          Γ ⊢tm whiskE w (suc e) c ∶ Λ w e k

  Ws : ∀ e → WTy e → WTy (suc e)
  Ws e W zero L c bd dc =
    subst (λ b → Γ ⊢tm whiskE L (suc (suc e)) c ∶
                   arr (Λ (srcW sd) e 0) (whiskE (srcW sd) (suc e) (cell b (dbl e))) (Tc e (suc (dbl e))))
          (cons-L sd e)
      (TR0 dZ (snd (genTy e bd)))
    where
    dZ : Γ ⊢tm whiskE (srcW sd) (suc e) c ∶ Λ (srcW sd) e 1
    dZ = W 1 (srcW sd) c bd (subst (λ b → Γ ⊢tm c ∶ Aty b (suc e)) (sym (cons-L sd e)) dc)
  Ws e W zero R c bd dc =
    subst (λ b → Γ ⊢tm whiskE R (suc (suc e)) c ∶
                   arr (Λ (tgtW sd) e 0) (Sc e (dbl e)) (whiskE (tgtW sd) (suc e) (cell b (suc (dbl e)))))
          (cons-R sd e)
      (TL0 dZ dg)
    where
    dZ : Γ ⊢tm whiskE (tgtW sd) (suc e) c ∶ Λ (tgtW sd) e 1
    dZ = W 1 (tgtW sd) c bd (subst (λ b → Γ ⊢tm c ∶ Aty b (suc e)) (sym (cons-R sd e)) dc)
    dg : Γ ⊢tm gen (dbl e) ∶ arr (Λ (tgtW sd) e 0) (Sc e (dbl e)) (Tc e (dbl e))
    dg = subst (λ X → Γ ⊢tm gen (dbl e) ∶ arr X (Sc e (dbl e)) (Tc e (dbl e)))
               (E' (srcW sd) (tgtW sd) e) (fst (genTy e bd))
  Ws e W (suc k) L c bd dc =
    subst (λ Y → Γ ⊢tm whiskE L (suc (suc e)) c ∶ Y) eqY
      (TR+ dZ dg (lt-Λ w' e k) (ty≡ w' e (suc k)) (tgt≡ w' e (suc k)))
    where
    w' = srcW sd
    bL = cpy sd L (suc (suc e))
    g = gen (suc (dbl e))
    dZ : Γ ⊢tm whiskE w' (suc e) c ∶ Λ w' e (suc (suc k))
    dZ = W (suc (suc k)) w' c (subst (λ n → T (suc n <ℕ suc m)) (ks k e) bd)
           (subst₂ (λ b n → Γ ⊢tm c ∶ Aty b (suc n)) (sym (cons-L sd e)) (ks k e) dc)
    dg : Γ ⊢tm g ∶ Gq e (suc (dbl e))
    dg = snd (genTy e (e<m k e bd))
    F : Bool → Nat → Tm × Tm
    F b n = whiskE L (suc (suc e)) (cell b (dbl n)) , whiskE L (suc (suc e)) (cell b (suc (dbl n)))
    pe : F (cpy sd w' (suc e)) (suc (k + e)) ≡ F bL (k + suc e)
    pe = cong₂ F (cons-L sd e) (sym (ks k e))
    ds₁ : Γ ⊢tm whiskE L (suc (suc e)) (cell bL (dbl (k + suc e))) ∶ Λ L (suc e) k
    ds₁ = Ws e W k L _ (<-suc (k + suc e) m bd) (fst (cellTy bL (k + suc e) bd))
    eqY : arr (tyE (fst (F (cpy sd w' (suc e)) (suc (k + e))))) (fst (F (cpy sd w' (suc e)) (suc (k + e))))
              (snd (F (cpy sd w' (suc e)) (suc (k + e))))
          ≡ Λ L (suc e) (suc k)
    eqY = trans (cong (λ P → arr (tyE (fst P)) (fst P) (snd P)) pe) (arr≡ (tyE-sound ds₁) refl refl)
  Ws e W (suc k) R c bd dc =
    subst (λ Y → Γ ⊢tm whiskE R (suc (suc e)) c ∶ Y) eqY
      (TL+ dZ dg (lt-Λ w' e k) (ty≡ w' e (suc k)) (src≡ w' e (suc k)))
    where
    w' = tgtW sd
    bR = cpy sd R (suc (suc e))
    g = gen (dbl e)
    dZ : Γ ⊢tm whiskE w' (suc e) c ∶ Λ w' e (suc (suc k))
    dZ = W (suc (suc k)) w' c (subst (λ n → T (suc n <ℕ suc m)) (ks k e) bd)
           (subst₂ (λ b n → Γ ⊢tm c ∶ Aty b (suc n)) (sym (cons-R sd e)) (ks k e) dc)
    dg : Γ ⊢tm g ∶ arr (Λ w' e 0) (Sc e (dbl e)) (Tc e (dbl e))
    dg = subst (λ X → Γ ⊢tm g ∶ arr X (Sc e (dbl e)) (Tc e (dbl e)))
               (E' (srcW sd) (tgtW sd) e) (fst (genTy e (e<m k e bd)))
    F : Bool → Nat → Tm × Tm
    F b n = whiskE R (suc (suc e)) (cell b (dbl n)) , whiskE R (suc (suc e)) (cell b (suc (dbl n)))
    pe : F (cpy sd w' (suc e)) (suc (k + e)) ≡ F bR (k + suc e)
    pe = cong₂ F (cons-R sd e) (sym (ks k e))
    ds₁ : Γ ⊢tm whiskE R (suc (suc e)) (cell bR (dbl (k + suc e))) ∶ Λ R (suc e) k
    ds₁ = Ws e W k R _ (<-suc (k + suc e) m bd) (fst (cellTy bR (k + suc e) bd))
    eqY : arr (tyE (fst (F (cpy sd w' (suc e)) (suc (k + e))))) (fst (F (cpy sd w' (suc e)) (suc (k + e))))
              (snd (F (cpy sd w' (suc e)) (suc (k + e))))
          ≡ Λ R (suc e) (suc k)
    eqY = trans (cong (λ P → arr (tyE (fst P)) (fst P) (snd P)) pe) (arr≡ (tyE-sound ds₁) refl refl)

  W : ∀ e → WTy e
  W zero    k w c _ dc = subst (Γ ⊢tm c ∶_) (sym (Λ0 w k)) dc
  W (suc e) = Ws e (W e)

  -- The top cell's whiskerings.
  top : (∀ b → Γ ⊢tm cell b (dbl m) ∶ Aty b m) →
        (Γ ⊢tm Sc m (dbl m) ∶ Λ (srcW sd) m 0) × (Γ ⊢tm Tc m (dbl m) ∶ Λ (srcW sd) m 0)
  top dx = W m 0 (srcW sd) _ (n<sn m) (dx _) ,
           subst (Γ ⊢tm Tc m (dbl m) ∶_) (E' (tgtW sd) (srcW sd) m) (W m 0 (tgtW sd) _ (n<sn m) (dx _))

  topTy≡ : (∀ b → Γ ⊢tm cell b (dbl m) ∶ Aty b m) →
           topTy m ≡ arr (Λ (srcW sd) m 0) (Sc m (dbl m)) (Tc m (dbl m))
  topTy≡ dx = cong (λ X → arr X (Sc m (dbl m)) (Tc m (dbl m))) (tyE-sound (fst (top dx)))

  topTy-wf : (∀ b → Γ ⊢tm cell b (dbl m) ∶ Aty b m) → Γ ⊢ty topTy m
  topTy-wf dx = subst (Γ ⊢ty_) (sym (topTy≡ dx)) (arr-wf (fst (top dx)) (snd (top dx)))

------------------------------------------------------------------------
-- Renaming the whiskerings of one disk prefix into another.

rn-sph : ∀ f C → rnSub f (sphSub C) ≡ sphSub (rnTy f C)
rn-sph f ⋆           = refl
rn-sph f (arr C s t) = cong (λ σ → σ ,ₛ rnTm f s ,ₛ rnTm f t) (rn-sph f C)

cohB≡ : ∀ {k k' j j' σ σ'} → k ≡ k' → j ≡ j' → σ ≡ σ' →
        coh (BK k j) (wK k j) σ ≡ coh (BK k' j') (wK k' j') σ'
cohB≡ refl refl refl = refl

cohL≡ : ∀ {k k' j j' σ σ'} → k ≡ k' → j ≡ j' → σ ≡ σ' →
        coh (LK k j) (lK k j) σ ≡ coh (LK k' j') (lK k' j') σ'
cohL≡ refl refl refl = refl

sd<d : ∀ k n → T (k <ℕ n) → T (suc (dbl k) <ℕ dbl n)
sd<d zero    (suc n) _ = tt
sd<d (suc k) (suc n) p = sd<d k n p

d<d : ∀ k n → T (k <ℕ n) → T (dbl k <ℕ dbl n)
d<d k n p = <-trans (dbl k) (suc (dbl k)) (dbl n) (n<sn (dbl k)) (sd<d k n p)

nB-pos : ∀ k j → T (k <ℕ nB k j)
nB-pos k zero    = n<sn k
nB-pos k (suc j) = <-suc k (suc (j + k)) (nB-pos k j)

suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
suc-inj refl = refl

module RnS (f : Nat → Nat) where
  rn-σLp : ∀ k j h x C → dim C ≡ nB k j →
           rnSub f (σLp k j h x C) ≡ σLp k j (rnTm f h) (rnTm f x) (rnTy f C)
  rn-σLp k zero h x C e =
    cong₂ (λ (P : Sub × Tm) Q → P .fst ,ₛ rnTm f x ,ₛ P .snd ,ₛ rnTm f h ,ₛ Q)
      (cong₂ _,_ (trans (rn-sph f (tyK k C)) (cong sphSub tyeq)) (lk (dbl k) (d<d k (dim C) kC)))
      (lk (suc (dbl k)) (sd<d k (dim C) kC))
    where
    kC : T (k <ℕ dim C)
    kC = subst (λ n → T (k <ℕ n)) (sym e) (nB-pos k zero)
    tyeq : rnTy f (tyK k C) ≡ tyK k (rnTy f C)
    tyeq = trans (rn-[]ty f (aL k) (sphSub C) (sc-aL-in k zero C e)) (cong (aL k [_]ty) (rn-sph f C))
    lk : ∀ i → T (i <ℕ dbl (dim C)) → rnTm f (lookupₛ (sphSub C) i) ≡ lookupₛ (sphSub (rnTy f C)) i
    lk i p = trans (rn-lookup f (sphSub C) i (subst (λ n → T (i <ℕ n)) (sym (lenₛ-sph C)) p))
                   (cong (λ σ → lookupₛ σ i) (rn-sph f C))
  rn-σLp k (suc j) h x ⋆ ()
  rn-σLp k (suc j) h x (arr C' s t) e =
    cong (λ σ → σ ,ₛ rnTm f s ,ₛ rnTm f t) (rn-σLp k j h x C' (suc-inj e))

module Rn (sd : Side) (Θ Θ' : Ctx) (Nq Nm q : Nat) (f : Nat → Nat)
  (wΘ' : Θ' ⊢ctx) (r : Resp f Θ Θ')
  (cellTy : ∀ b p → T (p <ℕ q) →
     (Θ ⊢tm G.cell sd Θ Nq b (dbl p) ∶ Lam.Aty sd Θ Nq b p) ×
     (Θ ⊢tm G.cell sd Θ Nq b (suc (dbl p)) ∶ Lam.Aty sd Θ Nq b p))
  (genTy : ∀ p → T (p <ℕ q) →
     (Θ ⊢tm G.gen sd Θ Nq (dbl p) ∶ Lam.Gq sd Θ Nq p (dbl p)) ×
     (Θ ⊢tm G.gen sd Θ Nq (suc (dbl p)) ∶ Lam.Gq sd Θ Nq p (suc (dbl p))))
  (f-cell : ∀ b v → T (v <ℕ dbl q) → rnTm f (G.cell sd Θ Nq b v) ≡ G.cell sd Θ' Nm b v)
  (f-gen : ∀ v → T (v <ℕ dbl q) → rnTm f (G.gen sd Θ Nq v) ≡ G.gen sd Θ' Nm v)
  where
  private
    module Q  = G sd Θ Nq
    module M  = G sd Θ' Nm
    module LQ = Lam sd Θ Nq
    module LM = Lam sd Θ' Nm
    module WQ = WL sd Θ Nq
    module WM = WL sd Θ' Nm
  open Wh sd Θ Nq q cellTy genTy using (W; lt-Λ; ks)
  open RnS f

  rn-rwE : ∀ {c h C B a z} → Θ ⊢tm c ∶ C → Θ ⊢tm h ∶ arr B a z →
           rnTm f (Q.rwE c h) ≡ M.rwE (rnTm f c) (rnTm f h)
  rn-rwE {c} {h} {C} {B} {a} {z} dc dh =
    trans (cong (rnTm f) (WQ.rwE≡ (WQ.tyE-sound dc) (WQ.tyE-sound dh)))
      (trans (cohB≡ (sym (rn-dim f B))
                    (cong₂ (λ u v → u ∸ suc v) (sym (rn-dim f C)) (sym (rn-dim f B)))
                    (cong (λ σ → σ ,ₛ rnTm f c ,ₛ rnTm f z ,ₛ rnTm f h) (rn-sph f C)))
             (sym (WM.rwE≡ (WM.tyE-sound (rn-tm wΘ' r dc)) (WM.tyE-sound (rn-tm wΘ' r dh)))))

  rn-lwE : ∀ {c h C B x y} → Θ ⊢tm c ∶ C → Θ ⊢tm h ∶ arr B x y → T (dim B <ℕ dim C) →
           rnTm f (Q.lwE h c) ≡ M.lwE (rnTm f h) (rnTm f c)
  rn-lwE {c} {h} {C} {B} {x} {y} dc dh lt =
    trans (cong (rnTm f) (WQ.lwE≡ (WQ.tyE-sound dc) (WQ.tyE-sound dh)))
      (trans (trans (cong (λ σ → coh (LK k j) (lK k j) (σ ,ₛ rnTm f c))
                          (rn-σLp k j h x C (nB-split k (dim C) lt)))
                    (cohL≡ {σ = σLp k j (rnTm f h) (rnTm f x) (rnTy f C) ,ₛ rnTm f c}
                       (sym (rn-dim f B))
                       (cong₂ (λ u v → u ∸ suc v) (sym (rn-dim f C)) (sym (rn-dim f B)))
                       (cong₂ (λ k' j' → σLp k' j' (rnTm f h) (rnTm f x) (rnTy f C) ,ₛ rnTm f c)
                              (sym (rn-dim f B))
                              (cong₂ (λ u v → u ∸ suc v) (sym (rn-dim f C)) (sym (rn-dim f B))))))
             (sym (WM.lwE≡ (WM.tyE-sound (rn-tm wΘ' r dc)) (WM.tyE-sound (rn-tm wΘ' r dh)))))
    where
    k = dim B
    j = dim C ∸ suc k

  e<q : ∀ k e → T (k + suc e <ℕ suc q) → T (e <ℕ q)
  e<q k e p = <-≤-trans e (k + suc e) q (subst (λ n → T (e <ℕ n)) (sym (ks k e)) (Lam.e<sk+e sd Θ Nq k e)) p

  rnW : ∀ e k w c → T (k + e <ℕ suc q) → Θ ⊢tm c ∶ LQ.Aty (cpy sd w (suc e)) (k + e) →
        rnTm f (Q.whiskE w (suc e) c) ≡ M.whiskE w (suc e) (rnTm f c)
  rnW zero    k w c _  _  = refl
  rnW (suc e) k L c bd dc =
    trans (rn-rwE dZ (snd (genTy e eq)))
          (cong₂ M.rwE (rnW e (suc k) (srcW sd) c bd' dc') (f-gen (suc (dbl e)) (sd<d e q eq)))
    where
    eq = e<q k e bd
    bd' : T (suc k + e <ℕ suc q)
    bd' = subst (λ n → T (n <ℕ suc q)) (ks k e) bd
    dc' : Θ ⊢tm c ∶ LQ.Aty (cpy sd (srcW sd) (suc e)) (suc k + e)
    dc' = subst₂ (λ b n → Θ ⊢tm c ∶ LQ.Aty b n) (sym (cons-L sd e)) (ks k e) dc
    dZ = W e (suc k) (srcW sd) c bd' dc'
  rnW (suc e) k R c bd dc =
    trans (rn-lwE dZ (fst (genTy e eq)) (subst₂ (λ a b → T (a <ℕ b)) (sym (LQ.dim-Λ (srcW sd) e 0)) (sym (LQ.dim-Λ (tgtW sd) e (suc k))) (LQ.e<sk+e k e)))
          (cong₂ M.lwE (f-gen (dbl e) (d<d e q eq)) (rnW e (suc k) (tgtW sd) c bd' dc'))
    where
    eq = e<q k e bd
    bd' : T (suc k + e <ℕ suc q)
    bd' = subst (λ n → T (n <ℕ suc q)) (ks k e) bd
    dc' : Θ ⊢tm c ∶ LQ.Aty (cpy sd (tgtW sd) (suc e)) (suc k + e)
    dc' = subst₂ (λ b n → Θ ⊢tm c ∶ LQ.Aty b n) (sym (cons-R sd e)) (ks k e) dc
    dZ = W e (suc k) (tgtW sd) c bd' dc'

  mutual
    rnΛ : ∀ w e k → T (k + e <ℕ suc q) → rnTy f (LQ.Λ w e k) ≡ LM.Λ w e k
    rnΛ w e zero    bd = rnB w e bd
    rnΛ w e (suc k) bd =
      arr≡ (rnΛ w e k bd₁)
           (trans (rnW e k w _ bd₁ (fst (cellTy b (k + e) bd)))
                  (cong (M.whiskE w (suc e)) (f-cell b (dbl (k + e)) (d<d (k + e) q bd))))
           (trans (rnW e k w _ bd₁ (snd (cellTy b (k + e) bd)))
                  (cong (M.whiskE w (suc e)) (f-cell b (suc (dbl (k + e))) (sd<d (k + e) q bd))))
      where
      b = cpy sd w (suc e)
      bd₁ = <-suc (k + e) q bd

    rnB : ∀ w e → T (e <ℕ suc q) → rnTy f (LQ.base w e) ≡ LM.base w e
    rnB w zero    _  = refl
    rnB L (suc e) bd =
      arr≡ (rnΛ (srcW sd) e 0 (<-suc e q bd))
           (trans (rnW e 0 (srcW sd) _ (<-suc e q bd)
                     (subst (λ b → Θ ⊢tm Q.cell (cpy sd L (suc (suc e))) (dbl e) ∶ LQ.Aty b e)
                            (sym (cons-L sd e)) (fst (cellTy (cpy sd L (suc (suc e))) e bd))))
                  (cong (M.whiskE (srcW sd) (suc e)) (f-cell _ (dbl e) (d<d e q bd))))
           (trans (rnW e 0 (tgtW sd) _ (<-suc e q bd) (snd (cellTy (cpy sd (tgtW sd) (suc e)) e bd)))
                  (cong (M.whiskE (tgtW sd) (suc e)) (f-cell _ (suc (dbl e)) (sd<d e q bd))))
    rnB R (suc e) bd =
      arr≡ (rnΛ (tgtW sd) e 0 (<-suc e q bd))
           (trans (rnW e 0 (srcW sd) _ (<-suc e q bd) (fst (cellTy (cpy sd (srcW sd) (suc e)) e bd)))
                  (cong (M.whiskE (srcW sd) (suc e)) (f-cell _ (dbl e) (d<d e q bd))))
           (trans (rnW e 0 (tgtW sd) _ (<-suc e q bd)
                     (subst (λ b → Θ ⊢tm Q.cell (cpy sd R (suc (suc e))) (suc (dbl e)) ∶ LQ.Aty b e)
                            (sym (cons-R sd e)) (snd (cellTy (cpy sd R (suc (suc e))) e bd))))
                  (cong (M.whiskE (tgtW sd) (suc e)) (f-cell _ (suc (dbl e)) (sd<d e q bd))))

  -- The type of the top generator of D^q, renamed.
  rnTop : (∀ b → Θ ⊢tm Q.cell b (dbl q) ∶ LQ.Aty b q) → ∀ y →
          (∀ b → rnTm f (Q.cell b (dbl q)) ≡ M.cell b y) →
          rnTy f (arr (LQ.Λ (srcW sd) q 0) (Q.Sc q (dbl q)) (Q.Tc q (dbl q))) ≡ LM.Gq q y
  rnTop dx y fy =
    arr≡ (rnΛ (srcW sd) q 0 (n<sn q))
         (trans (rnW q 0 (srcW sd) _ (n<sn q) (dx _)) (cong (M.whiskE (srcW sd) (suc q)) (fy _)))
         (trans (rnW q 0 (tgtW sd) _ (n<sn q) (dx _)) (cong (M.whiskE (tgtW sd) (suc q)) (fy _)))

------------------------------------------------------------------------
-- Disks are well formed and globular.

mk-Sph : ∀ k → mkCtx (dbl k) aD ≡ Sph k
mk-Sph zero    = refl
mk-Sph (suc k) = cong₂ _▸_ (cong₂ _▸_ (mk-Sph k) (cong aL (half-dbl k))) (cong aL (half-sdbl k))

Disk≡ : ∀ m → Disk m ≡ Dsk m
Disk≡ m = cong₂ _▸_ (mk-Sph m) (cong aL (half-dbl m))

Disk-wf : ∀ m → Disk m ⊢ctx
Disk-wf m = subst _⊢ctx (sym (Disk≡ m)) (fst (ps-wf (dsk-ps m)))

globTy-aL : ∀ k → globTy (aL k) ≡ true
globTy-aL zero    = refl
globTy-aL (suc k) = refl

glob-mk : ∀ n → globular (mkCtx n aD) ≡ true
glob-mk zero    = refl
glob-mk (suc n) rewrite glob-mk n | globTy-aL (half n) = refl

glob-Disk : ∀ m → T (globular (Disk m))
glob-Disk m = subst T (sym (glob-mk (suc (dbl m)))) tt

------------------------------------------------------------------------
-- T_m only reads T_j for j < m.

diskPre-ext : ∀ Ts Ts' m → (∀ j → T (j <ℕ m) → Ts j ≡ Ts' j) → diskPre Ts m ≡ diskPre Ts' m
diskPre-ext Ts Ts' m e = mk-ext (M + (M + dbl m)) go
  where
  M = suc (dbl m)
  go : ∀ i → T (i <ℕ M + (M + dbl m)) → gN Ts (Disk m) i ≡ gN Ts' (Disk m) i
  go i p with view3 M i
  ... | c0 q = trans (gD-c0 Ts m i q) (sym (gD-c0 Ts' m i q))
  ... | c1 d q refl = trans (gD-c1 Ts m d q) (sym (gD-c1 Ts' m d q))
  ... | c2 d refl =
    trans (gD-c2 Ts m d d<M)
          (trans (cong (rnTy (hmap M (suc (dbl (half d))) (chiK (Disk m) (half d) d))) (e (half d) (half-< d m d<)))
                 (sym (gD-c2 Ts' m d d<M)))
    where
    d< : T (d <ℕ dbl m)
    d< = +<-T M d (dbl m) (+<-T M (M + d) (M + dbl m) p)
    d<M : T (d <ℕ M)
    d<M = <-suc d (dbl m) d<

length-diskTysE : ∀ sd k → length (diskTysE sd k) ≡ suc k
length-diskTysE sd zero    = refl
length-diskTysE sd (suc k) = trans (length-snoc (diskTysE sd k) _) (cong suc (length-diskTysE sd k))

nth-last : ∀ As A n → length As ≡ n → nth (snocL As A) n ≡ A
nth-last []       A zero    _ = refl
nth-last (_ ∷ As) A (suc n) e = nth-last As A n (suc-inj e)

nth-diskTysE : ∀ sd k j → T (j <ℕ suc k) → nth (diskTysE sd k) j ≡ TsE sd j
nth-diskTysE sd zero    zero    _ = refl
nth-diskTysE sd (suc k) j p with j ==ℕ suc k in e
... | true  rewrite ==ℕ-sound j (suc k) (≡-T e) = refl
... | false =
  trans (nth-snoc (diskTysE sd k) _ j (subst (λ L → T (j <ℕ L)) (sym (length-diskTysE sd k))
                                             (<suc-≢ j (suc k) p e)))
        (nth-diskTysE sd k j (<suc-≢ j (suc k) p e))

TsE-step : ∀ sd m → TsE sd m ≡ StepTy sd (TsE sd) m
TsE-step sd zero    = refl
TsE-step sd (suc k) =
  trans (nth-last (diskTysE sd k) _ (suc k) (length-diskTysE sd k))
        (cong (λ Γ → G.topTy sd Γ (suc (dbl (suc k))) (suc k))
              (diskPre-ext (nth (diskTysE sd k)) (TsE sd) (suc k) (nth-diskTysE sd k)))

------------------------------------------------------------------------
-- The induction on m.

==-false' : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
==-false' zero    (suc b) _ = refl
==-false' (suc a) (suc b) p = ==-false' a b p

module Ind (sd : Side) where
  Ts : Nat → Ty
  Ts = TsE sd

  D : Nat → Ctx
  D m = diskPre Ts m

  Nn : Nat → Nat
  Nn m = suc (dbl m)

  module Gm (m : Nat) = G sd (D m) (Nn m)
  module Lm (m : Nat) = Lam sd (D m) (Nn m)

  CellTy GenTy : Nat → Set
  CellTy m = ∀ b p → T (p <ℕ m) →
             (D m ⊢tm Gm.cell m b (dbl p) ∶ Lm.Aty m b p) × (D m ⊢tm Gm.cell m b (suc (dbl p)) ∶ Lm.Aty m b p)
  GenTy m = ∀ q → T (q <ℕ m) →
            (D m ⊢tm Gm.gen m (dbl q) ∶ Lm.Gq m q (dbl q)) × (D m ⊢tm Gm.gen m (suc (dbl q)) ∶ Lm.Gq m q (suc (dbl q)))

  lenD : ∀ m → Nat
  lenD m = Nn m + (Nn m + dbl m)

  cellAt : ∀ m → D m ⊢ctx → ∀ b y → T (y <ℕ suc (dbl m)) → D m ⊢tm Gm.cell m b y ∶ Lm.Aty m b (half y)
  cellAt m w false y p =
    var-wf w (trans (lk-mk (lenD m) (gN Ts (Disk m)) y (lt-N y (Nn m) (Nn m + dbl m) p))
                    (cong just (gD-c0 Ts m y p)))
  cellAt m w true y p =
    var-wf w (trans (lk-mk (lenD m) (gN Ts (Disk m)) (Nn m + y) (T-+< (Nn m) y (Nn m + dbl m) (lt-N y (Nn m) (dbl m) p)))
                    (cong just (gD-c1 Ts m y p)))

  cellTyOf : ∀ m → D m ⊢ctx → CellTy m
  cellTyOf m w b p lt =
    subst (λ n → D m ⊢tm Gm.cell m b (dbl p) ∶ Lm.Aty m b n) (half-dbl p)
          (cellAt m w b (dbl p) (<-suc (dbl p) (dbl m) (d<d p m lt))) ,
    subst (λ n → D m ⊢tm Gm.cell m b (suc (dbl p)) ∶ Lm.Aty m b n) (half-sdbl p)
          (cellAt m w b (suc (dbl p)) (d<d p m lt))

  topCell : ∀ m → D m ⊢ctx → ∀ b → D m ⊢tm Gm.cell m b (dbl m) ∶ Lm.Aty m b m
  topCell m w b = subst (λ n → D m ⊢tm Gm.cell m b (dbl m) ∶ Lm.Aty m b n) (half-dbl m)
                        (cellAt m w b (dbl m) (n<sn (dbl m)))

  record Good (m : Nat) : Set where
    field
      wf   : D m ⊢ctx
      gens : GenTy m

  module WhG (m : Nat) (g : Good m) = Wh sd (D m) (Nn m) m (cellTyOf m (Good.wf g)) (Good.gens g)

  TsE-wf-at : ∀ m → Good m → D m ⊢ty Ts m
  TsE-wf-at m g = subst (D m ⊢ty_) (sym (TsE-step sd m)) (WhG.topTy-wf m g (topCell m (Good.wf g)))

  TsE-form : ∀ m → Good m → Ts m ≡ arr (Lm.Λ m (srcW sd) m 0) (Gm.Sc m m (dbl m)) (Gm.Tc m m (dbl m))
  TsE-form m g = trans (TsE-step sd m) (WhG.topTy≡ m g (topCell m (Good.wf g)))

  Good0 : Good 0
  Good0 = record { wf = ▸-wf w1 (⋆-wf w1) ; gens = λ q () }
    where
    w1 = ▸-wf ε-wf (⋆-wf ε-wf)

  module Step (k : Nat) (IH : ∀ j → T (j <ℕ suc k) → Good j) where
    mt = suc k
    N  = Nn mt

    dk : ∀ x → T (x <ℕ dbl mt) → T (dimV (Disk mt) x <ℕ suc k)
    dk x p = subst (λ h → T (h <ℕ mt)) (sym (dimV-D mt x (<-suc x (dbl mt) p))) (half-< x mt p)

    BN : T (dbl mt <ℕ suc (len (Disk mt)))
    BN = subst (λ L → T (dbl mt <ℕ suc L)) (sym (len-D mt)) (<-dbl mt)

    module M' = Main Ts k (λ j p → TsE-wf-at j (IH j p)) (Disk mt) (Disk-wf mt) (glob-Disk mt) (dbl mt) BN dk

    wf : D mt ⊢ctx
    wf = subst (λ L → mkCtx (L + (L + dbl mt)) (gN Ts (Disk mt)) ⊢ctx) (len-D mt) M'.prefix-wf

    module _ (y : Nat) (py : T (y <ℕ dbl mt)) where
      q = half y
      qlt : T (q <ℕ mt)
      qlt = half-< y mt py
      gq = IH q qlt
      wq = Good.wf gq
      y<M : T (y <ℕ suc (dbl mt))
      y<M = <-suc y (dbl mt) py
      f : Nat → Nat
      f = hmap N (suc (dbl q)) (chiK (Disk mt) q y)

      RespAt : Nat → Nat → Set
      RespAt N' q' = Resp (hmap N' (suc (dbl q')) (chiK (Disk mt) q' y)) (diskPre Ts q')
                          (mkCtx (N' + (N' + y)) (gN Ts (Disk mt)))

      r : Resp f (D q) (D mt)
      r i A eq = lk-prefix (N + (N + y)) (gN Ts (Disk mt)) (f i)
                   (subst₂ RespAt (len-D mt) (dimV-D mt y y<M) (M'.C2.r y py) i A eq)
                   (lenD mt) (<-suc (N + (N + y)) (lenD mt) (T-+< N (N + y) (N + dbl mt) (T-+< N y (dbl mt) py)))

      χv : ∀ v → T (v <ℕ dbl q) → chiK (Disk mt) q y v ≡ v
      χv v pv = trans (Classify.chiD (Disk mt) (Disk-wf mt) (glob-Disk mt) mt q y v y<M refl
                                     (<-suc v (dbl q) pv))
                      (cong (λ b → if b then y else v) (==-false' v (dbl q) pv))
      χtop : chiK (Disk mt) q y (dbl q) ≡ y
      χtop = trans (Classify.chiD (Disk mt) (Disk-wf mt) (glob-Disk mt) mt q y (dbl q) y<M refl (n<sn (dbl q)))
                   (cong (λ b → if b then y else dbl q) (==-refl (dbl q)))

      M = suc (dbl q)
      χ : Nat → Nat
      χ = chiK (Disk mt) q y
      f-cell : ∀ b v → T (v <ℕ dbl q) → rnTm f (Gm.cell q b v) ≡ Gm.cell mt b v
      f-cell false v pv = cong var (trans (hmap-c0 N M χ v (<-suc v (dbl q) pv)) (χv v pv))
      f-cell true  v pv = cong var (trans (hmap-c1 N M χ v (<-suc v (dbl q) pv)) (cong (N +_) (χv v pv)))
      f-gen : ∀ v → T (v <ℕ dbl q) → rnTm f (Gm.gen q v) ≡ Gm.gen mt v
      f-gen v pv = cong var (trans (hmap-c2 N M χ v) (cong (λ z → N + (N + z)) (χv v pv)))
      f-top : ∀ b → rnTm f (Gm.cell q b (dbl q)) ≡ Gm.cell mt b y
      f-top false = cong var (trans (hmap-c0 N M χ (dbl q) (n<sn (dbl q))) χtop)
      f-top true  = cong var (trans (hmap-c1 N M χ (dbl q) (n<sn (dbl q))) (cong (N +_) χtop))

      module R = Rn sd (D q) (D mt) (Nn q) N q f wf r (cellTyOf q wq) (Good.gens gq) f-cell f-gen

      genAt : D mt ⊢tm Gm.gen mt y ∶ Lm.Gq mt q y
      genAt = var-wf wf
        (trans (lk-mk (lenD mt) (gN Ts (Disk mt)) (N + (N + y)) (T-+< N (N + y) (N + dbl mt) (T-+< N y (dbl mt) py)))
               (cong just (trans (gD-c2 Ts mt y y<M)
                          (trans (cong (rnTy f) (TsE-form q gq))
                                 (R.rnTop (topCell q wq) y f-top)))))

    good : Good mt
    good = record
      { wf = wf
      ; gens = λ q' pq →
          subst (λ n → D mt ⊢tm Gm.gen mt (dbl q') ∶ Lm.Gq mt n (dbl q')) (half-dbl q')
                (genAt (dbl q') (d<d q' mt pq)) ,
          subst (λ n → D mt ⊢tm Gm.gen mt (suc (dbl q')) ∶ Lm.Gq mt n (suc (dbl q'))) (half-sdbl q')
                (genAt (suc (dbl q')) (sd<d q' mt pq))
      }

  Good< : ∀ n m → T (m <ℕ n) → Good m
  Good< (suc n) zero    _ = Good0
  Good< (suc n) (suc k) p = Step.good k (λ j pj → Good< n j (≤-<-trans j k n pj p))

  good : ∀ m → Good m
  good m = Good< (suc m) m (n<sn m)

------------------------------------------------------------------------
-- The theorem.

-- The top generator of every disk cylinder D^m ⊗ D¹ (right) and
-- D¹ ⊗ D^m (left) is well typed.
TsE-wf : ∀ sd m → diskPre (TsE sd) m ⊢ty TsE sd m
TsE-wf sd m = Ind.TsE-wf-at sd m (Ind.good sd m)

-- Γ ⊗ D¹ (right) and D¹ ⊗ Γ (left), for globular Γ of any dimension.
cylE : Side → Ctx → Ctx
cylE sd Γ = cylWith (TsE sd) Γ

-- D13: the cylinder of every well-formed globular context is well formed.
cylE-wf : ∀ sd Γ → Γ ⊢ctx → T (globular Γ) → cylE sd Γ ⊢ctx
cylE-wf sd Γ w gl =
  Main.cylWith-wf (TsE sd) (dimCtx Γ) (λ j _ → TsE-wf sd j) Γ w gl (len Γ) (n<sn (len Γ))
    (λ x p → dimV-≤ Γ x p) refl
