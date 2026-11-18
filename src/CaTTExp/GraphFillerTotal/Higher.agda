------------------------------------------------------------------------
-- Totality of the discreteness filler on cells of dimension ≥ 2 in a
-- graph context (open-issues F2a, higher cells).
--
-- Γ is a graph context: no variable has dimension ≥ 2. For every two
-- parallel cells
--
--     Γ ⊢ u ∶ A      Γ ⊢ v ∶ A      with dim A ≥ 1,
--
-- the term  fillN Γ u v A  is a well-typed cell u → v (Theorem
-- `totalN`). No hypothesis on paths is needed: parallel cells of
-- dimension ≥ 2 share their 1-dimensional source, hence their path.
-- Together with CaTTExp.GraphFillerTotal (1-cells, with equal paths)
-- this is the discreteness filler of `ordinary-math.md` §3 in every
-- dimension.
--
-- The filler is the canonical lift into the chain Θ_k, now for cells
-- of any dimension:
--
--   fillN Γ u v A = coh Θ_k (liftTy A 0 k →  lift u 0 → lift v 0) [σ]
--
-- where k is the length of the path of A's 1-dimensional source and σ
-- walks along that path. A coh over a pasting context Θ is lifted
-- argument by argument; the argument at a variable of Θ is lifted at the
-- position of that variable's leftmost object, which is the length of
-- the path (in Γ) from the image of Θ's first object to the image of
-- that object (`pp`).
--
-- The proof:
--   * path invariant (`PI`): a 2-cell s ⇒ t of Γ has path s = path t,
--     so parallel edges of a pasting context get the same path (`pedge`);
--   * the path of the image of a 1-cell of Θ joins the positions of its
--     ends (`D'`);
--   * the range lemma (CaTTExp.GraphFillerTotal.Range): a valid
--     coherence's type spans its whole pasting context, so the lift
--     starts at the right position and stays inside Θ_k;
--   * lifting commutes with substitution (`comm`), which makes the
--     lifted arguments well typed (`liftN-ty`), and substituting σ back
--     gives the original cell (`liftN-sub`).
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotal.Higher where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal.Chains
open import CaTTExp.GraphFillerTotal
open import CaTTExp.GraphFillerTotal.Range
open import CaTTExp.PureMetatheory using (closed; ty[]; tm[]; sub∘)
import CaTTExp.Subst ∅ cattSide as S

------------------------------------------------------------------------
-- Graph contexts.

Graph : Ctx → Set
Graph Γ = ∀ i {A s t u v} → lookup Γ i ≡ just (arr (arr A s t) u v) → ⊥

------------------------------------------------------------------------
-- Positions: the path from the first object of a pasting context to
-- (the leftmost object of) each variable, under a substitution τ.

upd : (Nat → List Nat) → Nat → List Nat → List Nat → Nat → List Nat
upd P n a b i = if i ==ℕ n then a else (if i ==ℕ suc n then b else P i)

pp : Ctx → Sub → Nat → List Nat
pp (Θ ▸ ⋆ ▸ arr _ (var x) _) (τ ,ₛ _ ,ₛ f) =
  upd (pp Θ τ) (len Θ) (pp Θ τ x ++ path f) (pp Θ τ x)
pp (Θ ▸ arr _ _ _ ▸ arr _ (var x) _) (τ ,ₛ _ ,ₛ _) =
  upd (pp Θ τ) (len Θ) (pp Θ τ x) (pp Θ τ x)
pp _ _ = λ _ → []

-- The path of the 1-dimensional source of a cell t : A.
π : Ty → Tm → List Nat
π (arr (arr B s t) u v) _ = π (arr B s t) u
π _                     t = path t

------------------------------------------------------------------------
-- The lift.

mutual
  liftN : Tm → Nat → Tm
  liftN (var _)     o = var (edge (suc o))
  liftN (coh Θ A τ) o = coh Θ A (liftSN Θ τ o)
  liftN (cst ())    o

  liftSN : Ctx → Sub → Nat → Sub
  liftSN (Θ ▸ ⋆ ▸ arr _ (var x) _) (τ ,ₛ _ ,ₛ f) o =
    liftSN Θ τ o ,ₛ var (vtx (∣ path f ∣ + (∣ pp Θ τ x ∣ + o))) ,ₛ liftN f (∣ pp Θ τ x ∣ + o)
  liftSN (Θ ▸ arr _ _ _ ▸ arr _ (var x) _) (τ ,ₛ y ,ₛ f) o =
    liftSN Θ τ o ,ₛ liftN y (∣ pp Θ τ x ∣ + o) ,ₛ liftN f (∣ pp Θ τ x ∣ + o)
  liftSN _ (⟨⟩ ,ₛ _) o = ⟨⟩ ,ₛ var (vtx o)
  liftSN _ _         o = ⟨⟩

liftTy : Ty → Nat → Nat → Ty
liftTy ⋆                     o o' = ⋆
liftTy (arr ⋆ _ _)           o o' = arr ⋆ (var (vtx o)) (var (vtx o'))
liftTy (arr (arr B s t) u v) o o' = arr (liftTy (arr B s t) o o') (liftN u o) (liftN v o)

------------------------------------------------------------------------
-- Small facts.

private
  arr-inj₁ : ∀ {A B t u t' u'} → arr A t u ≡ arr B t' u' → A ≡ B
  arr-inj₁ refl = refl
  arr-inj₂ : ∀ {A B t u t' u'} → arr A t u ≡ arr B t' u' → t ≡ t'
  arr-inj₂ refl = refl
  arr-inj₃ : ∀ {A B t u t' u'} → arr A t u ≡ arr B t' u' → u ≡ u'
  arr-inj₃ refl = refl
  var-inj : ∀ {i j} → var i ≡ var j → i ≡ j
  var-inj refl = refl

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  ⋆-sub : ∀ A τ → A [ τ ]ty ≡ ⋆ → A ≡ ⋆
  ⋆-sub ⋆ τ _ = refl
  ⋆-sub (arr _ _ _) τ ()

  sn≢ : ∀ n → (suc n ==ℕ n) ≡ false
  sn≢ zero    = refl
  sn≢ (suc n) = sn≢ n

upd-n : ∀ P n a b → upd P n a b n ≡ a
upd-n P n a b rewrite ==-refl n = refl

upd-sn : ∀ P n a b → upd P n a b (suc n) ≡ b
upd-sn P n a b rewrite sn≢ n | ==-refl n = refl

upd-old : ∀ P n a b i → i < n → upd P n a b i ≡ P i
upd-old P n a b i h rewrite <→≢ h | <→≢ (≤-step h) = refl

++-cancel : ∀ (p q r : List Nat) → p ++ q ≡ p ++ r → q ≡ r
++-cancel []      q r e = e
++-cancel (x ∷ p) q r e = ++-cancel p q r (tail-eq e)
  where
  tail-eq : ∀ {a : Nat} {xs ys} → a ∷ xs ≡ a ∷ ys → xs ≡ ys
  tail-eq refl = refl

-- Lengths of substitutions and their lifts.
sub-len' : ∀ {Γ τ Θ} → Γ ⊢sub τ ∶ Θ → lenₛ τ ≡ len Θ
sub-len' s = snd (S.sub-sc closed s)

------------------------------------------------------------------------
-- On chains, the new lift is the old one.

pp-chain : ∀ {Γ} k τ → Γ ⊢sub τ ∶ chainC k → pp (chainC k) τ (vtx k) ≡ pathCh τ
pp-chain zero (⟨⟩ ,ₛ x) _ = refl
pp-chain zero (_ ,ₛ _ ,ₛ _) (,-wf () _)
pp-chain (suc k) (τ ,ₛ x ,ₛ e) (,-wf (,-wf s _) _) =
  trans (cong (upd (pp (chainC k) τ) (len (chainC k)) (pp (chainC k) τ (vtx k) ++ path e)
                   (pp (chainC k) τ (vtx k))) (sym (len-chain k)))
   (trans (upd-n (pp (chainC k) τ) (len (chainC k)) _ _)
          (cong (_++ path e) (pp-chain k τ s)))

mutual
  liftN-eq : ∀ {Γ B a b} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → liftN u o ≡ lift u o
  liftN-eq (var _) o _ _ = refl
  liftN-eq (coh Θ A τ) o d eq with coh-view d eq
  ... | cohV k _ _ _ _ s _ _ = cong (coh Θ A) (liftSN-chain k τ o s)
  liftN-eq (cst ()) _ _ _

  liftSN-chain : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k → liftSN (chainC k) τ o ≡ liftCh τ o
  liftSN-chain zero (⟨⟩ ,ₛ x) o _ = refl
  liftSN-chain zero (_ ,ₛ _ ,ₛ _) o (,-wf () _)
  liftSN-chain (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) de)
    rewrite pp-chain k τ s =
    cong₂ (λ a b → a ,ₛ var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o))) ,ₛ b)
      (liftSN-chain k τ o s) (liftN-eq e (∣ pathCh τ ∣ + o) de refl)

------------------------------------------------------------------------
-- The path invariant.

-- Positions grow along each edge of Θ by the path of its image.
PEdge : Ctx → Sub → Set
PEdge Θ τ = ∀ e c d → lookup Θ e ≡ just (arr ⋆ (var c) (var d)) →
            pp Θ τ d ≡ pp Θ τ c ++ path (lookupₛ τ e)

-- And then along every 1-cell of Θ.
mutual
  D' : ∀ {Θ Γ τ} → PEdge Θ τ → Γ ⊢sub τ ∶ Θ → ∀ t {B a b} → Θ ⊢tm t ∶ B →
       B ≡ arr ⋆ (var a) (var b) → pp Θ τ b ≡ pp Θ τ a ++ path (t [ τ ]tm)
  D' pe sτ (var e) (var-wf _ le) refl = pe e _ _ le
  D' pe sτ (coh Θ' A ρ) d eq with coh-view d eq
  ... | cohV k _ _ _ _ s ea eb = D'Ch pe sτ k ρ s ea eb
  D' pe sτ (cst ()) _ _

  D'Ch : ∀ {Θ Γ τ} → PEdge Θ τ → Γ ⊢sub τ ∶ Θ → ∀ k ρ → Θ ⊢sub ρ ∶ chainC k → ∀ {a b} →
         lookupₛ ρ 0 ≡ var a → lookupₛ ρ (vtx k) ≡ var b →
         pp Θ τ b ≡ pp Θ τ a ++ pathCh (ρ ∘ τ)
  D'Ch {Θ} {τ = τ} pe sτ zero (⟨⟩ ,ₛ x) _ {a} ea eb =
    trans (cong (pp Θ τ) (var-inj (trans (sym eb) ea))) (sym (++-[] (pp Θ τ a)))
  D'Ch pe sτ zero (_ ,ₛ _ ,ₛ _) (,-wf () _) _ _
  D'Ch {Θ} {τ = τ} pe sτ (suc k) (ρ ,ₛ y ,ₛ e) (,-wf (,-wf s dy) de) {a} {b} ea eb
    with last-var s | ⋆-var dy refl
  ... | w , lw | z , refl =
    trans (cong (pp Θ τ) (sym zb))
     (trans (D' pe sτ e de (trans (edge-ty s) (cong (λ t → arr ⋆ t (var z)) lw)))
      (trans (cong (_++ path (e [ τ ]tm)) (D'Ch pe sτ k ρ s ea' lw))
             (++-assoc (pp Θ τ a) (pathCh (ρ ∘ τ)) (path (e [ τ ]tm)))))
    where
    ea' : lookupₛ ρ 0 ≡ var a
    ea' = trans (sym (lookupₛ-there₂ ρ (var z) e 0 (zero< s))) ea
    zb : z ≡ b
    zb = var-inj (trans (sym (last-obj s)) eb)

private
  lk₂-top : ∀ {Γ Θ τ y f} → Γ ⊢sub τ ∶ Θ → lookupₛ (τ ,ₛ y ,ₛ f) (suc (len Θ)) ≡ f
  lk₂-top {τ = τ} {y} {f} s = lookupₛ-here (τ ,ₛ y) f _ (cong suc (sym (sub-len' s)))

  lk₂-mid : ∀ {Γ Θ τ y f} → Γ ⊢sub τ ∶ Θ → lookupₛ (τ ,ₛ y ,ₛ f) (len Θ) ≡ y
  lk₂-mid {Θ = Θ} {τ} {y} {f} s =
    trans (lookupₛ-there (τ ,ₛ y) f (len Θ) (subst (len Θ <_) (cong suc (sym (sub-len' s))) ≤-refl))
          (lookupₛ-here τ y (len Θ) (sym (sub-len' s)))

  lk₂-old : ∀ {Γ Θ τ y f i} → Γ ⊢sub τ ∶ Θ → i < len Θ → lookupₛ (τ ,ₛ y ,ₛ f) i ≡ lookupₛ τ i
  lk₂-old {τ = τ} {y} {f} {i} s h = lookupₛ-there₂ τ y f i (subst (i <_) (sym (sub-len' s)) h)

  lk₁-old : ∀ {Γ Θ τ y i} → Γ ⊢sub τ ∶ Θ → i < len Θ → lookupₛ (τ ,ₛ y) i ≡ lookupₛ τ i
  lk₁-old {τ = τ} {y} {i} s h = lookupₛ-there τ y i (subst (i <_) (sym (sub-len' s)) h)

  ps-one : ∀ {B x A} → (ε ▸ B) ⊢ps x ∶ A → B ≡ ⋆
  ps-one pss     = refl
  ps-one (psd d) = ps-one d

  obj-lt : ∀ {Θ c} → lookup Θ c ≡ just ⋆ → c < len Θ
  obj-lt {Θ} = lookup-< {Θ}

mutual
  PI : ∀ {Γ B a b s t} → Graph Γ → ∀ α → Γ ⊢tm α ∶ B → B ≡ arr (arr ⋆ a b) s t → path s ≡ path t
  PI gr (var i) (var-wf _ eq) refl = ⊥-elim (gr i eq)
  PI gr (coh Θ (arr ⋆ s' t') τ) (coh-wf _ _ _ _ _) eq with arr-inj₁ eq
  ... | ()
  PI gr (coh Θ (arr (arr X u v) s' t') τ) (coh-wf (ps p₀) w (arr-wf ds' dt') ok sτ) eq
    with ⋆-sub X τ (arr-inj₁ (arr-inj₁ eq)) | tm-ty ds'
  ... | refl | arr-wf du dv with ⋆-var du refl | ⋆-var dv refl
  ...   | a' , refl | b' , refl =
    trans (cong path (sym (arr-inj₂ eq)))
     (trans (++-cancel (pp Θ τ a') _ _ (trans (sym e1) e2)) (cong path (arr-inj₃ eq)))
    where
    pe = pedge gr p₀ τ sτ
    e1 = D' pe sτ s' ds' refl
    e2 = D' pe sτ t' dt' refl
  PI gr (cst ()) _ _

  pedge : ∀ {Γ Θ x A} → Graph Γ → Θ ⊢ps x ∶ A → ∀ τ → Γ ⊢sub τ ∶ Θ → PEdge Θ τ
  pedge gr p ⟨⟩ (⟨⟩-wf _) e c d ()
  pedge gr p (⟨⟩ ,ₛ y) (,-wf (⟨⟩-wf _) _) e c d le with lookup-cases ε _ e le | ps-one p
  ... | inj₁ (_ , refl) | ()
  ... | inj₂ (() , _) | _
  pedge gr p (τ ,ₛ y ,ₛ f) (,-wf (,-wf sτ dy) df) with ps-inv p
  ... | x' , p' , refl = pedge-step gr p' τ y f sτ dy df (pedge gr p' τ sτ)

  pedge-step : ∀ {Γ Θ₀ x' B} → Graph Γ → Θ₀ ⊢ps x' ∶ B → ∀ τ y f → Γ ⊢sub τ ∶ Θ₀ →
               Γ ⊢tm y ∶ B [ τ ]ty → Γ ⊢tm f ∶ arr B (var x') (var (len Θ₀)) [ τ ,ₛ y ]ty →
               PEdge Θ₀ τ → PEdge (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ ,ₛ y ,ₛ f)
  pedge-step {Θ₀ = Θ₀} {x'} {⋆} gr p' τ y f sτ dy df ih e c d le
    with lookup-cases (Θ₀ ▸ ⋆) (arr ⋆ (var x') (var (len Θ₀))) e le
  ... | inj₁ (refl , refl) =
    trans (upd-n P n _ _)
     (sym (trans (cong₂ _++_ (upd-old P n _ _ x' (obj-lt {Θ₀} (snd (good p'))))
                              (cong path (lk₂-top {y = y} {f} sτ))) refl))
    where
    P = pp Θ₀ τ
    n = len Θ₀
  ... | inj₂ (_ , le') with lookup-cases Θ₀ ⋆ e le'
  ...   | inj₁ (_ , ())
  ...   | inj₂ (e< , le'') with fst (good p') e _ le''
  ...     | lc , ld =
    trans (upd-old P n _ _ d (obj-lt {Θ₀} ld))
     (trans (ih e c d le'')
      (cong₂ _++_ (sym (upd-old P n _ _ c (obj-lt {Θ₀} lc)))
                  (cong path (sym (lk₂-old {y = y} {f} sτ e<)))))
    where
    P = pp Θ₀ τ
    n = len Θ₀
  pedge-step {Θ₀ = Θ₀} {x'} {arr B₀ s₀ t₀} gr p' τ y f sτ dy df ih e c d le
    with lookup-cases (Θ₀ ▸ arr B₀ s₀ t₀) (arr (arr B₀ s₀ t₀) (var x') (var (len Θ₀))) e le
  ... | inj₁ (_ , eqC) with arr-inj₁ eqC
  ...   | ()
  pedge-step {Θ₀ = Θ₀} {x'} {arr B₀ s₀ t₀} gr p' τ y f sτ dy df ih e c d le
    | inj₂ (_ , le') with lookup-cases Θ₀ (arr B₀ s₀ t₀) e le'
  ...   | inj₁ (refl , refl) with fst (good p') x' _ (snd (good p'))
  ...     | lc , ld =
    trans (upd-old P n _ _ d (obj-lt {Θ₀} ld))
     (trans (ih x' c d (snd (good p')))
      (cong₂ _++_ (sym (upd-old P n _ _ c (obj-lt {Θ₀} lc)))
        (trans (PI gr f df refl')
               (cong path (trans (lookupₛ-here τ y (len Θ₀) (sym (sub-len' sτ)))
                                 (sym (lk₂-mid {y = y} {f} sτ)))))))
    where
    P = pp Θ₀ τ
    n = len Θ₀
    refl' : arr (arr ⋆ (var c) (var d)) (var x') (var (len Θ₀)) [ τ ,ₛ y ]ty
            ≡ arr (arr ⋆ (lookupₛ (τ ,ₛ y) c) (lookupₛ (τ ,ₛ y) d)) (lookupₛ τ x') (lookupₛ (τ ,ₛ y) (len Θ₀))
    refl' = cong (λ z → arr (arr ⋆ (lookupₛ (τ ,ₛ y) c) (lookupₛ (τ ,ₛ y) d)) z (lookupₛ (τ ,ₛ y) (len Θ₀)))
                 (lk₁-old {y = y} sτ (obj-lt' {Θ₀} (snd (good p'))))
      where
      obj-lt' : ∀ {Θ i B} → lookup Θ i ≡ just B → i < len Θ
      obj-lt' {Θ} = lookup-< {Θ}
  pedge-step {Θ₀ = Θ₀} {x'} {arr B₀ s₀ t₀} gr p' τ y f sτ dy df ih e c d le
    | inj₂ (_ , le') | inj₂ (e< , le'') with fst (good p') e _ le''
  ...     | lc , ld =
    trans (upd-old P n _ _ d (obj-lt {Θ₀} ld))
     (trans (ih e c d le'')
      (cong₂ _++_ (sym (upd-old P n _ _ c (obj-lt {Θ₀} lc)))
                  (cong path (sym (lk₂-old {y = y} {f} sτ e<)))))
    where
    P = pp Θ₀ τ
    n = len Θ₀
