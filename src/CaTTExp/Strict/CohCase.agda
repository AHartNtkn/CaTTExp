------------------------------------------------------------------------
-- The coherence case of strict-model soundness without hypotheses.
--
-- Soundness's coherence case needs: two cells t, u : A of ν(K(Δ)) from
-- the first to the last object of a pasting context Δ, whose closed
-- supports both equal that of the total cell T, have equal top chains.
-- With n = dim of their top chains and d = dimK (homs Δ):
--
--   n = 0      both are single tuples w, w'; w lies in the closure of
--              {w'}, and w' has rank 0, so w = w';
--   0 < n < d  impossible: T's top table is inhabited, its tuples have
--              rank d, and they would lie below a tuple of t of
--              rank ≤ n;
--   n = d      the boundary is injective on top-degree chains
--              (Strict.TopCell.top-inj);
--   n > d      no tuple from the first to the last object has degree
--              n (Strict.TopCell.deg-bound), so both top chains are
--              empty.
------------------------------------------------------------------------
module CaTTExp.Strict.CohCase where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Strict.Complex
open import CaTTExp.Strict.Cell
open import CaTTExp.Strict.L
open import CaTTExp.Strict.Hyp using (SetEq; flat-supp; twT; ⊆T-sound; endsV→endsTy; inv-gr)
open import CaTTExp.Strict.Pasting using (_∈_; hd∈; tl∈; hom-ends; objL)
open import CaTTExp.Strict.Bridge using (T-cell; posOf-complete; objs-objL; ∈-pairs-snd'; le-trans)
open import CaTTExp.Strict.TopCell
open import CaTTExp.Gray.Pure hiding (Tuple)
open import CaTTExp.Gray.Cover using (_≤_; z≤n; s≤s; Any) renaming (here to hereA; there to thereA)
open import CaTTExp.Gray.SetFacts ∅ using (_∈L_)
open import CaTTExp.Gray.DownAgree ∅ using (memT-sound; memT-complete; nub-sound; nub-complete) renaming (module Faces to DF)
import CaTTExp.Gray.Graded ∅ as Gr

------------------------------------------------------------------------
-- Ranks of composable tuples are their degrees.

rank-deg : ∀ {Γ} → Γ ⊢ps → ∀ x y w → WFT Γ x y w → DF.rank (cells Γ) w ≡ deg Γ w
rank-deg P x y [] _ = refl
rank-deg {Γ} P x y (v ∷ w) (z , ev , p) with endsL-inv (lookup Γ v) ev
... | (A , lv , evA) = cong₂ _+_ hv (rank-deg P z y w p)
  where
  pk = posOf-complete z (objs Γ) (subst (z ∈_) (sym (objs-objL Γ)) (∈-pairs-snd' (objL Γ) (hom-ends P v ev)))
  hv : DF.hgt (cells Γ) v ≡ hdimV Γ v
  hv = trans (Gr.hgt-pos Γ v lv (endsV→endsTy A evA) (snd pk)) (cong hdimTy (sym lv))

------------------------------------------------------------------------
-- Every tuple of a cell's table is a basis element of degree ≤ n.

BasLe : Ctx → Nat → Nat → Nat → Tuple → Set
BasLe Γ x y n s = Σ Nat λ k → T (k <ℕ suc n) × Basis Γ x y k s

flat-bas : ∀ Γ x y n X → IsCellL Γ x y n X → All (BasLe Γ x y n) (flat X)
flat-bas Γ x y zero    (base c)     (w , p , b) = All-≈ (w ∷ []) c (≈-sym p) ((0 , tt , b) , tt)
flat-bas Γ x y zero    (step _ _ _) ()
flat-bas Γ x y (suc n) (base _)     ()
flat-bas Γ x y (suc n) (step S U c) (cS , cU , _ , _ , a) =
  All-++ (flat S) (flat U ++ c) (All-map (flat S) wk (flat-bas Γ x y n S cS))
    (All-++ (flat U) c (All-map (flat U) wk (flat-bas Γ x y n U cU))
      (All-map c (λ s b → suc n , n<suc (suc n) , b) a))
  where
  wk : ∀ s → BasLe Γ x y n s → BasLe Γ x y (suc n) s
  wk s (k , l , b) = k , <-suc k (suc n) l , b

All-∈L : ∀ {P : Tuple → Set} X {x} → All P X → x ∈L X → P x
All-∈L (y ∷ X) (p , _)  (hereA refl) = p
All-∈L (y ∷ X) (_ , qs) (thereA m)   = All-∈L X qs m

count-∈L : ∀ a X → Pos (count a X) → a ∈L X
count-∈L a []      ()
count-∈L a (x ∷ X) p with eqT a x in e
... | true  = hereA (eqT-sound a x (subst T (sym e) tt))
... | false = thereA (count-∈L a X p)

∈L-++r : ∀ A {B x} → x ∈L B → x ∈L (A ++ B)
∈L-++r []      m = m
∈L-++r (_ ∷ A) m = thereA (∈L-++r A m)

------------------------------------------------------------------------
-- Arithmetic.

sum0r : ∀ a b → a + b ≡ 0 → b ≡ 0
sum0r zero    b e = e
sum0r (suc a) b ()

lt-le : ∀ b c a → T (b <ℕ c) → T (c <ℕ suc a) → T (b <ℕ a)
lt-le zero    (suc c) zero    _ ()
lt-le zero    (suc c) (suc a) _ _ = tt
lt-le (suc b) (suc c) zero    _ ()
lt-le (suc b) (suc c) (suc a) p q = lt-le b c a p q
lt-le zero    zero    _ () _
lt-le (suc b) zero    _ () _

cmp : ∀ a b → T (a <ℕ b) ⊎ ((a ≡ b) ⊎ T (b <ℕ a))
cmp zero    zero    = inj₂ (inj₁ refl)
cmp zero    (suc b) = inj₁ tt
cmp (suc a) zero    = inj₂ (inj₂ tt)
cmp (suc a) (suc b) with cmp a b
... | inj₁ p        = inj₁ p
... | inj₂ (inj₁ e) = inj₂ (inj₁ (cong suc e))
... | inj₂ (inj₂ p) = inj₂ (inj₂ p)

empty-of : ∀ {P : Tuple → Set} X → All P X → (∀ s → P s → ⊥) → X ≡ []
empty-of []      _       _ = refl
empty-of (x ∷ X) (p , _) f = ⊥-elim (f x p)

------------------------------------------------------------------------
-- The level-0 table of a cell is inhabited.

base-elem : ∀ Γ x y hs sg n → IsCellL Γ x y n (twT hs sg n) → Σ Bool λ b → Σ Tuple λ w → w ∈L chainT b 0 hs
base-elem Γ x y hs sg zero    (w , p , _) =
  sg , w , count-∈L w (chainT sg 0 hs) (subst Pos (sym (at p w)) (subst Pos (sym (eqT-refl' w)) tt))
  where
  eqT-refl' : ∀ w → count w (w ∷ []) ≡ 1
  eqT-refl' w = cong (λ b → if b then 1 else 0) (eqT-refl w)
base-elem Γ x y hs sg (suc n) (cS , _) = base-elem Γ x y hs false n cS

------------------------------------------------------------------------
-- Endpoints.

endsOK-eq : ∀ Γ A {x y} → endsTy A ≡ just (var x , var y) →
            endsOK Γ A ≡ ((x ==ℕ firstL (objs Γ)) ∧ (y ==ℕ lastL (objs Γ)))
endsOK-eq Γ A e rewrite e = refl

ends-obj : ∀ Γ A {x y} → endsV A ≡ just (x , y) → T (endsOK Γ A) →
           (x ≡ firstL (objs Γ)) × (y ≡ lastL (objs Γ))
ends-obj Γ A {x} {y} e ok =
  ==ℕ-sound x _ (∧-fst q) , ==ℕ-sound y _ (∧-snd {x ==ℕ firstL (objs Γ)} q)
  where
  q = subst T (endsOK-eq Γ A (endsV→endsTy A e)) ok

------------------------------------------------------------------------
-- The theorem.

module _ {Δ : Ctx} (P : Δ ⊢ps) where
  private
    hs = homs Δ
    d  = dimK hs
    cs = cells Δ
    G  = Gr.graded Δ (inv-gr (psInv P))
    module F = DF cs

  reach0 : ∀ {s x} → F.Reach 0 s x → s ≡ x
  reach0 F.done = refl

  down-in : ∀ S {x} → x ∈L S → T (memT x (down Δ S))
  down-in S {x} m = memT-complete x _ (F.close⇐ d (nubT S) (x , nub-complete S m , 0 , z≤n , F.done))

  down-out : ∀ S {x} → T (memT x (down Δ S)) → Σ Tuple λ s → (s ∈L S) × Σ Nat λ k → F.Reach k s x
  down-out S {x} m with F.close⇒ d (nubT S) (memT-sound x _ m)
  ... | s , ms , k , _ , r = s , nub-sound S ms , k , r

  ≈T-l : ∀ D₁ D₂ {x} → T (≈T D₁ D₂) → T (memT x D₁) → T (memT x D₂)
  ≈T-l D₁ D₂ {x} p = ⊆T-sound D₁ D₂ (∧-fst p) x

  ≈T-r : ∀ D₁ D₂ {x} → T (≈T D₁ D₂) → T (memT x D₂) → T (memT x D₁)
  ≈T-r D₁ D₂ {x} p = ⊆T-sound D₂ D₁ (∧-snd {⊆T D₁ D₂} p) x

  bas' : ∀ {e₁ e₂ k s} A → T (endsOK Δ A) → endsV A ≡ just (e₁ , e₂) → Basis Δ e₁ e₂ k s →
         Basis Δ (firstL (objs Δ)) (lastL (objs Δ)) k s
  bas' {k = k} {s} A ok ee = subst₂ (λ x y → Basis Δ x y k s) (fst (ends-obj Δ A ee ok)) (snd (ends-obj Δ A ee ok))

  coh-top : ∀ A₀ a₀ b₀ t u e₁ e₂ → T (endsOK Δ (arr A₀ a₀ b₀)) → endsV (arr A₀ a₀ b₀) ≡ just (e₁ , e₂) →
            IsCellL Δ e₁ e₂ (dim A₀) (towerOf t (arr A₀ a₀ b₀)) →
            IsCellL Δ e₁ e₂ (dim A₀) (towerOf u (arr A₀ a₀ b₀)) →
            T (≈T (down Δ (supp t (arr A₀ a₀ b₀))) (down Δ (fullT hs))) →
            T (≈T (down Δ (supp u (arr A₀ a₀ b₀))) (down Δ (fullT hs))) →
            top (towerOf t (arr A₀ a₀ b₀)) ≈ top (towerOf u (arr A₀ a₀ b₀))
  -- n = 0.
  coh-top ⋆ a₀ b₀ t u e₁ e₂ ok ee (w , pw , bw) (w' , pw' , bw') pt pu =
    ≈-trans pw (subst (λ z → (z ∷ []) ≈ topS u) (sym ww') (≈-sym pw'))
    where
    A = arr ⋆ a₀ b₀
    m1 : T (memT w (supp t A))
    m1 = subst T (flat-supp t ⋆ a₀ b₀ w)
           (memT-complete w (topS t) (count-∈L w (topS t) (subst Pos (sym (at pw w)) (subst Pos (sym (cong (λ b → if b then 1 else 0) (eqT-refl w))) tt))))
    m2 : T (memT w (down Δ (supp u A)))
    m2 = ≈T-r (down Δ (supp u A)) (down Δ (fullT hs)) {w} pu (≈T-l (down Δ (supp t A)) (down Δ (fullT hs)) {w} pt (down-in (supp t A) {w} (memT-sound w (supp t A) m1)))
    allw' : All (λ s → s ≡ w') (topS u)
    allw' = All-≈ (w' ∷ []) (topS u) (≈-sym pw') (refl , tt)
    D = down-out (supp u A) {w} m2
    sd = fst D
    r = snd (snd (snd D))
    sw' : sd ≡ w'
    sw' = All-∈L (topS u) allw'
            (memT-sound sd _ (subst T (sym (flat-supp u ⋆ a₀ b₀ sd)) (memT-complete sd _ (fst (snd D)))))
    k0 : fst (snd (snd D)) ≡ 0
    k0 = sum0r (F.rank w) _ (trans (F.reach-rank G r)
           (trans (cong F.rank sw') (trans (rank-deg P e₁ e₂ w' (fst bw')) (snd bw'))))
    ww' : w ≡ w'
    ww' = trans (sym (reach0 (subst (λ j → F.Reach j sd w) k0 r))) sw'

  -- n ≥ 1.
  coh-top (arr B a b) a₀ b₀ t u e₁ e₂ ok ee cT@(cS , cU0 , _ , chT , atT) (_ , _ , _ , chU , atU) pt pu
    with cmp d (suc (dim B))
  ... | inj₁ dlt = ≡→≈ (trans (empty-of (topS t) atT big) (sym (empty-of (topS u) atU big)))
    where
    big : ∀ s → Basis Δ e₁ e₂ (suc (dim B)) s → ⊥
    big s bs = lt-le-absurd d (suc (dim B)) dlt (deg-bound P s (suc (dim B)) (bas' (arr (arr B a b) a₀ b₀) ok ee bs))
  ... | inj₂ (inj₁ deq) =
    top-inj P dpos (topS t) (topS u) _ _ (All-map (topS t) up atT) (All-map (topS u) up atU) chT chU
    where
    dpos : T (0 <ℕ d)
    dpos = subst (λ z → T (0 <ℕ z)) (sym deq) tt
    up : ∀ s → Basis Δ e₁ e₂ (suc (dim B)) s → TopInj.Top P dpos s
    up s bs = subst (λ k → Basis Δ (firstL (objs Δ)) (lastL (objs Δ)) k s) (sym deq) (bas' (arr (arr B a b) a₀ b₀) ok ee bs)
  ... | inj₂ (inj₂ ltd) = ⊥-elim (lt-le-absurd k' d k'<d d≤k')
    where
    A = arr (arr B a b) a₀ b₀
    Tc = T-cell P A e₁ e₂ ok (endsV→endsTy A ee)
    B0 = base-elem Δ e₁ e₂ hs true d Tc
    X = Gr.Ranks.top-ne Δ (fst B0) true (snd (snd B0))
    x = fst X
    rx : F.rank x ≡ d
    rx = Gr.Ranks.chain-rank Δ true d {x} (snd X)
    m2 : T (memT x (down Δ (supp t A)))
    m2 = ≈T-r (down Δ (supp t A)) (down Δ (fullT hs)) {x} pt (down-in (fullT hs) {x} (∈L-++r (lowerT d hs) (snd X)))
    D = down-out (supp t A) {x} m2
    s = fst D
    k = fst (snd (snd D))
    r = snd (snd (snd D))
    BS : BasLe Δ e₁ e₂ (suc (dim B)) s
    BS = All-∈L (flat (towerOf t A)) {s} (flat-bas Δ e₁ e₂ (suc (dim B)) (towerOf t A) cT)
           (memT-sound s (flat (towerOf t A)) (subst T (sym (flat-supp t (arr B a b) a₀ b₀ s)) (memT-complete s (supp t A) (fst (snd D)))))
    k' = fst BS
    dk : d + k ≡ k'
    dk = trans (cong (_+ k) (sym rx))
           (trans (F.reach-rank G r) (trans (rank-deg P e₁ e₂ s (fst (snd (snd BS)))) (snd (snd (snd BS)))))
    k'<d : T (k' <ℕ d)
    k'<d = le-trans (suc k') (suc (suc (dim B))) d (fst (snd BS)) ltd
    d≤k' : T (d <ℕ suc k')
    d≤k' = subst (λ z → T (d <ℕ suc z)) (trans (+-comm k d) dk) (le-+l k d)
