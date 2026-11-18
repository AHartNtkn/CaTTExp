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
open import CaTTExp.Weakening ∅ cattSide using (wk-ty)
import CaTTExp.Subst ∅ cattSide as S

------------------------------------------------------------------------
-- Graph contexts.

Graph : Ctx → Set
Graph Γ = ∀ i {A s t u v} → lookup Γ i ≡ just (arr (arr A s t) u v) → ⊥

-- Being a graph context is decidable.
isGraph : Ctx → Bool
isGraph ε                         = true
isGraph (Γ ▸ ⋆)                   = isGraph Γ
isGraph (Γ ▸ arr ⋆ _ _)           = isGraph Γ
isGraph (Γ ▸ arr (arr _ _ _) _ _) = false

isGraph-ok : ∀ Γ → T (isGraph Γ) → Graph Γ
isGraph-ok ε _ i ()
isGraph-ok (Γ ▸ ⋆) h i eq with i ==ℕ len Γ
isGraph-ok (Γ ▸ ⋆) h i () | true
isGraph-ok (Γ ▸ ⋆) h i eq | false = isGraph-ok Γ h i eq
isGraph-ok (Γ ▸ arr ⋆ _ _) h i eq with i ==ℕ len Γ
isGraph-ok (Γ ▸ arr ⋆ _ _) h i () | true
isGraph-ok (Γ ▸ arr ⋆ _ _) h i eq | false = isGraph-ok Γ h i eq
isGraph-ok (Γ ▸ arr (arr _ _ _) _ _) () i eq

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

------------------------------------------------------------------------
-- The lifted substitution, entry by entry.

private
  ∣++∣+ : ∀ p q o → ∣ p ++ q ∣ + o ≡ ∣ q ∣ + (∣ p ∣ + o)
  ∣++∣+ p q o = trans (cong (_+ o) (trans (∣++∣ p q) (+-comm ∣ p ∣ ∣ q ∣))) (+-assoc ∣ q ∣ ∣ p ∣ o)

  good-o₀ : ∀ {Θ} → Good Θ → ∀ {j} B s t → lookup Θ j ≡ just (arr B s t) →
            lookup Θ (o₀Ty (arr B s t)) ≡ just ⋆
  good-o₀ g B s t lj with g _ _ lj
  ... | vs , vt with s
  ...   | var c with B
  ...     | ⋆ = vs
  ...     | arr B' s' t' = good-o₀ g B' s' t' vs

mutual
  lenL : ∀ {Γ Θ x A} → Θ ⊢ps x ∶ A → ∀ τ o → Γ ⊢sub τ ∶ Θ → lenₛ (liftSN Θ τ o) ≡ len Θ
  lenL p ⟨⟩ o (⟨⟩-wf _) = refl
  lenL p (⟨⟩ ,ₛ a) o (,-wf (⟨⟩-wf _) _) = refl
  lenL p (τ ,ₛ y ,ₛ f) o (,-wf (,-wf sτ _) _) with ps-inv p
  ... | x' , p' , refl = lenL-step _ τ y f o p' sτ

  lenL-step : ∀ {Γ} B {Θ₀ x'} τ y f o → Θ₀ ⊢ps x' ∶ B → Γ ⊢sub τ ∶ Θ₀ →
              lenₛ (liftSN (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ ,ₛ y ,ₛ f) o) ≡ suc (suc (len Θ₀))
  lenL-step ⋆           τ y f o p' s = cong (λ n → suc (suc n)) (lenL p' τ o s)
  lenL-step (arr _ _ _) τ y f o p' s = cong (λ n → suc (suc n)) (lenL p' τ o s)

lk-top2 : ∀ σ a b {n} → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a ,ₛ b) (suc n) ≡ b
lk-top2 σ a b l = lookupₛ-here (σ ,ₛ a) b _ (cong suc (sym l))

lk-mid2 : ∀ σ a b {n} → lenₛ σ ≡ n → lookupₛ (σ ,ₛ a ,ₛ b) n ≡ a
lk-mid2 σ a b {n} l =
  trans (lookupₛ-there (σ ,ₛ a) b n (subst (n <_) (cong suc (sym l)) ≤-refl))
        (lookupₛ-here σ a n (sym l))

lk-old2 : ∀ σ a b {n i} → lenₛ σ ≡ n → i < n → lookupₛ (σ ,ₛ a ,ₛ b) i ≡ lookupₛ σ i
lk-old2 σ a b {i = i} l h = lookupₛ-there₂ σ a b i (subst (i <_) (sym l) h)

EntObj : Ctx → Sub → Nat → Nat → Set
EntObj Θ τ o j = lookupₛ (liftSN Θ τ o) j ≡ var (vtx (∣ pp Θ τ j ∣ + o))

EntArr : Ctx → Sub → Nat → Nat → Ty → Set
EntArr Θ τ o j B = (lookupₛ (liftSN Θ τ o) j ≡ liftN (lookupₛ τ j) (∣ pp Θ τ j ∣ + o)) ×
                   (pp Θ τ j ≡ pp Θ τ (o₀Ty B))

Ent : Ctx → Sub → Nat → Set
Ent Θ τ o = ∀ j → (lookup Θ j ≡ just ⋆ → EntObj Θ τ o j) ×
                  (∀ {B s t} → lookup Θ j ≡ just (arr B s t) → EntArr Θ τ o j (arr B s t))

mutual
  ent : ∀ {Γ Θ x A} → Θ ⊢ps x ∶ A → ∀ τ o → Γ ⊢sub τ ∶ Θ → Ent Θ τ o
  ent p ⟨⟩ o (⟨⟩-wf _) j = (λ ()) , (λ ())
  ent p (⟨⟩ ,ₛ a) o (,-wf (⟨⟩-wf _) _) j with ps-one p
  ... | refl = obj , arr'
    where
    obj : lookup (ε ▸ ⋆) j ≡ just ⋆ → EntObj (ε ▸ ⋆) (⟨⟩ ,ₛ a) o j
    obj lj with lookup-cases ε ⋆ j lj
    ... | inj₁ (refl , _) = refl
    ... | inj₂ (() , _)
    arr' : ∀ {B s t} → lookup (ε ▸ ⋆) j ≡ just (arr B s t) → EntArr (ε ▸ ⋆) (⟨⟩ ,ₛ a) o j (arr B s t)
    arr' lj with lookup-cases ε ⋆ j lj
    ... | inj₁ (_ , ())
    ... | inj₂ (() , _)
  ent p (τ ,ₛ y ,ₛ f) o (,-wf (,-wf sτ _) _) with ps-inv p
  ... | x' , p' , refl = ent-step _ p' τ y f o sτ (ent p' τ o sτ)

  ent-step : ∀ {Γ} B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → ∀ τ y f o → Γ ⊢sub τ ∶ Θ₀ → Ent Θ₀ τ o →
             Ent (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ ,ₛ y ,ₛ f) o
  ent-step ⋆ {Θ₀} {x'} p' τ y f o sτ ih j = obj , arr'
    where
    n  = len Θ₀
    P  = pp Θ₀ τ
    L  = liftSN Θ₀ τ o
    ln = lenL p' τ o sτ
    lτ = sub-len' sτ
    g  = fst (good p')
    x<n : x' < n
    x<n = obj-lt {Θ₀} (snd (good p'))
    C  = arr ⋆ (var x') (var n)
    obj : lookup (Θ₀ ▸ ⋆ ▸ C) j ≡ just ⋆ → EntObj (Θ₀ ▸ ⋆ ▸ C) (τ ,ₛ y ,ₛ f) o j
    obj lj with lookup-cases (Θ₀ ▸ ⋆) C j lj
    ... | inj₁ (_ , ())
    ... | inj₂ (_ , lj') with lookup-cases Θ₀ ⋆ j lj'
    ...   | inj₁ (refl , _) =
            trans (lk-mid2 L _ _ ln)
              (cong (λ m → var (vtx m))
                (sym (trans (cong (λ q → ∣ q ∣ + o) (upd-n P n (P x' ++ path f) (P x')))
                            (∣++∣+ (P x') (path f) o))))
    ...   | inj₂ (j< , lj'') =
            trans (lk-old2 L _ _ ln j<)
              (trans (fst (ih j) lj'')
                (cong (λ q → var (vtx (∣ q ∣ + o))) (sym (upd-old P n _ _ j j<))))
    arr' : ∀ {B s t} → lookup (Θ₀ ▸ ⋆ ▸ C) j ≡ just (arr B s t) → EntArr (Θ₀ ▸ ⋆ ▸ C) (τ ,ₛ y ,ₛ f) o j (arr B s t)
    arr' lj with lookup-cases (Θ₀ ▸ ⋆) C j lj
    ... | inj₁ (refl , refl) =
          trans (lk-top2 L _ _ ln)
            (cong₂ liftN (sym (lk-top2 τ y f lτ))
                         (cong (λ q → ∣ q ∣ + o) (sym (upd-sn P n (P x' ++ path f) (P x'))))) ,
          trans (upd-sn P n _ _) (sym (upd-old P n _ _ x' x<n))
    ... | inj₂ (_ , lj') with lookup-cases Θ₀ ⋆ j lj'
    ...   | inj₁ (_ , ())
    ...   | inj₂ (j< , lj'') =
            trans (lk-old2 L _ _ ln j<)
              (trans (fst (snd (ih j) lj''))
                (cong₂ liftN (sym (lk-old2 τ y f lτ j<))
                             (cong (λ q → ∣ q ∣ + o) (sym (upd-old P n _ _ j j<))))) ,
            trans (upd-old P n _ _ j j<)
              (trans (snd (snd (ih j) lj''))
                (sym (upd-old P n _ _ _ (obj-lt {Θ₀} (good-o₀ g _ _ _ lj'')))))
  ent-step (arr B₀ s₀ t₀) {Θ₀} {x'} p' τ y f o sτ ih j = obj , arr'
    where
    n  = len Θ₀
    P  = pp Θ₀ τ
    L  = liftSN Θ₀ τ o
    ln = lenL p' τ o sτ
    lτ = sub-len' sτ
    g  = fst (good p')
    B  = arr B₀ s₀ t₀
    lx = snd (good p')
    C  = arr B (var x') (var n)
    o<n : o₀Ty B < n
    o<n = obj-lt {Θ₀} (good-o₀ g B₀ s₀ t₀ lx)
    xo : pp (Θ₀ ▸ B ▸ C) (τ ,ₛ y ,ₛ f) x' ≡ pp (Θ₀ ▸ B ▸ C) (τ ,ₛ y ,ₛ f) (o₀Ty B)
    xo = trans (upd-old P n _ _ x' (lookup-< {Θ₀} lx))
           (trans (snd (snd (ih x') lx)) (sym (upd-old P n _ _ _ o<n)))
    obj : lookup (Θ₀ ▸ B ▸ C) j ≡ just ⋆ → EntObj (Θ₀ ▸ B ▸ C) (τ ,ₛ y ,ₛ f) o j
    obj lj with lookup-cases (Θ₀ ▸ B) C j lj
    ... | inj₁ (_ , ())
    ... | inj₂ (_ , lj') with lookup-cases Θ₀ B j lj'
    ...   | inj₁ (_ , ())
    ...   | inj₂ (j< , lj'') =
            trans (lk-old2 L _ _ ln j<)
              (trans (fst (ih j) lj'')
                (cong (λ q → var (vtx (∣ q ∣ + o))) (sym (upd-old P n _ _ j j<))))
    arr' : ∀ {B' s t} → lookup (Θ₀ ▸ B ▸ C) j ≡ just (arr B' s t) → EntArr (Θ₀ ▸ B ▸ C) (τ ,ₛ y ,ₛ f) o j (arr B' s t)
    arr' lj with lookup-cases (Θ₀ ▸ B) C j lj
    ... | inj₁ (refl , refl) =
          trans (lk-top2 L _ _ ln)
            (cong₂ liftN (sym (lk-top2 τ y f lτ))
                         (cong (λ q → ∣ q ∣ + o) (sym (upd-sn P n (P x') (P x'))))) ,
          trans (upd-sn P n _ _) (trans (sym (upd-old P n (P x') (P x') x' (lookup-< {Θ₀} lx))) xo)
    ... | inj₂ (_ , lj') with lookup-cases Θ₀ B j lj'
    ...   | inj₁ (refl , refl) =
            trans (lk-mid2 L _ _ ln)
              (cong₂ liftN (sym (lk-mid2 τ y f lτ))
                           (cong (λ q → ∣ q ∣ + o) (sym (upd-n P n (P x') (P x'))))) ,
            trans (upd-n P n _ _) (trans (sym (upd-old P n (P x') (P x') x' (lookup-< {Θ₀} lx))) xo)
    ...   | inj₂ (j< , lj'') =
            trans (lk-old2 L _ _ ln j<)
              (trans (fst (snd (ih j) lj''))
                (cong₂ liftN (sym (lk-old2 τ y f lτ j<))
                             (cong (λ q → ∣ q ∣ + o) (sym (upd-old P n _ _ j j<))))) ,
            trans (upd-old P n _ _ j j<)
              (trans (snd (snd (ih j) lj''))
                (sym (upd-old P n _ _ _ (obj-lt {Θ₀} (good-o₀ g _ _ _ lj'')))))

------------------------------------------------------------------------
-- Positions: the first object, walks, and lengths.

mutual
  pp-0 : ∀ {Γ Θ x A} → Θ ⊢ps x ∶ A → ∀ τ → Γ ⊢sub τ ∶ Θ → pp Θ τ 0 ≡ []
  pp-0 p ⟨⟩ (⟨⟩-wf _) = refl
  pp-0 p (⟨⟩ ,ₛ a) (,-wf (⟨⟩-wf _) _) with ps-one p
  ... | refl = refl
  pp-0 p (τ ,ₛ y ,ₛ f) (,-wf (,-wf sτ _) _) with ps-inv p
  ... | x' , p' , refl = pp-0-step _ p' τ y f sτ

  pp-0-step : ∀ {Γ} B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → ∀ τ y f → Γ ⊢sub τ ∶ Θ₀ →
              pp (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ ,ₛ y ,ₛ f) 0 ≡ []
  pp-0-step ⋆ {Θ₀} {x'} p' τ y f s =
    trans (upd-old (pp Θ₀ τ) (len Θ₀) (pp Θ₀ τ x' ++ path f) (pp Θ₀ τ x') 0 (lookup-< {Θ₀} (ps-0 p'))) (pp-0 p' τ s)
  pp-0-step (arr _ _ _) {Θ₀} {x'} p' τ y f s =
    trans (upd-old (pp Θ₀ τ) (len Θ₀) (pp Θ₀ τ x') (pp Θ₀ τ x') 0 (lookup-< {Θ₀} (ps-0 p'))) (pp-0 p' τ s)

mono-pp : ∀ {Θ τ} → PEdge Θ τ → Mono Θ (pp Θ τ)
mono-pp {τ = τ} pe e c d le = path (lookupₛ τ e) , pe e c d le

-- The positions of the objects are walks from the image of the first.
mutual
  walkpp : ∀ {Γ Θ x A} → Θ ⊢ps x ∶ A → Θ ⊢ctx → ∀ τ → Γ ⊢sub τ ∶ Θ → ∀ c → lookup Θ c ≡ just ⋆ →
           Walk Γ (vi (lookupₛ τ 0)) (pp Θ τ c) (vi (lookupₛ τ c))
  walkpp p w ⟨⟩ (⟨⟩-wf _) c ()
  walkpp p w (⟨⟩ ,ₛ a) (,-wf (⟨⟩-wf _) _) c lc with ps-one p
  ... | refl with lookup-cases ε ⋆ c lc
  ...   | inj₁ (refl , _) = nil
  ...   | inj₂ (() , _)
  walkpp p (▸-wf (▸-wf w₀ _) _) (τ ,ₛ y ,ₛ f) (,-wf (,-wf sτ dy) df) with ps-inv p
  ... | x' , p' , refl = walkpp-step _ p' w₀ τ y f sτ dy df (walkpp p' w₀ τ sτ)

  walkpp-step : ∀ {Γ} B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → Θ₀ ⊢ctx → ∀ τ y f → Γ ⊢sub τ ∶ Θ₀ →
                Γ ⊢tm y ∶ B [ τ ]ty → Γ ⊢tm f ∶ arr B (var x') (var (len Θ₀)) [ τ ,ₛ y ]ty →
                (∀ c → lookup Θ₀ c ≡ just ⋆ → Walk Γ (vi (lookupₛ τ 0)) (pp Θ₀ τ c) (vi (lookupₛ τ c))) →
                ∀ c → lookup (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) c ≡ just ⋆ →
                Walk Γ (vi (lookupₛ (τ ,ₛ y ,ₛ f) 0)) (pp (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ ,ₛ y ,ₛ f) c)
                     (vi (lookupₛ (τ ,ₛ y ,ₛ f) c))
  walkpp-step {Γ} ⋆ {Θ₀} {x'} p' w₀ τ y f sτ dy df ih c lc
    with lookup-cases (Θ₀ ▸ ⋆) (arr ⋆ (var x') (var (len Θ₀))) c lc
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , lc') with lookup-cases Θ₀ ⋆ c lc'
  ...   | inj₂ (c< , lc'') =
    subst₃ (Walk Γ) (cong vi (sym (lk-old2 τ y f lτ 0<n)))
                    (sym (upd-old (pp Θ₀ τ) n _ _ c c<)) (cong vi (sym (lk-old2 τ y f lτ c<)))
      (ih c lc'')
    where
    n   = len Θ₀
    lτ  = sub-len' sτ
    0<n : 0 < n
    0<n = lookup-< {Θ₀} (ps-0 p')
    subst₃ : ∀ {A B C : Set} (R : A → B → C → Set) {a a' b b' c c'} →
             a ≡ a' → b ≡ b' → c ≡ c' → R a b c → R a' b' c'
    subst₃ R refl refl refl r = r
  ...   | inj₁ (refl , _) with ⋆-var (S.lookup-sub closed w₀ (snd (good p')) sτ) refl | ⋆-var dy refl
  ...     | wv , ew | z , refl =
    subst₃ (Walk Γ) (cong vi (sym (lk-old2 τ (var z) f lτ 0<n)))
                    (sym (upd-n (pp Θ₀ τ) n _ _)) (cong vi (sym (lk-mid2 τ (var z) f lτ)))
      (walk-++ (subst (λ t → Walk Γ (vi (lookupₛ τ 0)) (pp Θ₀ τ x') (vi t)) ew (ih x' lx))
               (walk f df (cong₂ (arr ⋆)
                            (trans (lk₁-old {y = var z} sτ (lookup-< {Θ₀} lx)) ew')
                            (lookupₛ-here τ (var z) (len Θ₀) (sym lτ)))))
    where
    n   = len Θ₀
    lx  = snd (good p')
    lτ  = sub-len' sτ
    0<n : 0 < n
    0<n = lookup-< {Θ₀} (ps-0 p')
    ew' : lookupₛ τ x' ≡ var wv
    ew' = ew
    subst₃ : ∀ {A B C : Set} (R : A → B → C → Set) {a a' b b' c c'} →
             a ≡ a' → b ≡ b' → c ≡ c' → R a b c → R a' b' c'
    subst₃ R refl refl refl r = r
  walkpp-step {Γ} (arr B₀ s₀ t₀) {Θ₀} {x'} p' w₀ τ y f sτ dy df ih c lc
    with lookup-cases (Θ₀ ▸ arr B₀ s₀ t₀) (arr (arr B₀ s₀ t₀) (var x') (var (len Θ₀))) c lc
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , lc') with lookup-cases Θ₀ (arr B₀ s₀ t₀) c lc'
  ...   | inj₁ (_ , ())
  ...   | inj₂ (c< , lc'') =
    subst₃ (Walk Γ) (cong vi (sym (lk-old2 τ y f lτ 0<n)))
                    (sym (upd-old (pp Θ₀ τ) n _ _ c c<)) (cong vi (sym (lk-old2 τ y f lτ c<)))
      (ih c lc'')
    where
    n   = len Θ₀
    lτ  = sub-len' sτ
    0<n : 0 < n
    0<n = lookup-< {Θ₀} (ps-0 p')
    subst₃ : ∀ {A B C : Set} (R : A → B → C → Set) {a a' b b' c c'} →
             a ≡ a' → b ≡ b' → c ≡ c' → R a b c → R a' b' c'
    subst₃ R refl refl refl r = r

-- The path of the 1-dimensional source of the image of a cell of Θ
-- joins the positions of its end objects.
πty : ∀ {Θ Γ τ} → PEdge Θ τ → Γ ⊢sub τ ∶ Θ → ∀ B s → Θ ⊢tm s ∶ B → NS B →
      pp Θ τ (o₁Ty B) ≡ pp Θ τ (o₀Ty B) ++ π (B [ τ ]ty) (s [ τ ]tm)
πty pe sτ (arr ⋆ a b) s ds _ with tm-ty ds
... | arr-wf da db with ⋆-var da refl | ⋆-var db refl
...   | a' , refl | b' , refl = D' pe sτ s ds refl
πty pe sτ (arr (arr B' s₀ t₀) a b) s ds _ = πty pe sτ (arr B' s₀ t₀) a (arr-l (tm-ty ds)) tt
  where
  arr-l : ∀ {Θ A a b} → Θ ⊢ty arr A a b → Θ ⊢tm a ∶ A
  arr-l (arr-wf da _) = da

------------------------------------------------------------------------
-- Lifting commutes with substitution.

private
  var-obj : ∀ {Θ m} → Θ ⊢tm var m ∶ ⋆ → lookup Θ m ≡ just ⋆
  var-obj (var-wf _ e) = e

  ⊑-self : ∀ p q → p ++ q ⊑ p → q ≡ []
  ⊑-self p q (r , e) with ++-cancel p [] (q ++ r) (trans (++-[] p) (trans e (++-assoc p q r)))
  ⊑-self p []      (r , e) | _ = refl
  ⊑-self p (x ∷ q) (r , e) | ()

module Comm {Γ Θ x₀ A₀} (τ : Sub) (o : Nat) (sτ : Γ ⊢sub τ ∶ Θ) (pΘ : Θ ⊢ps x₀ ∶ A₀)
            (wΘ : Θ ⊢ctx) (pe : PEdge Θ τ) where

  P = pp Θ τ
  L = liftSN Θ τ o
  E = ent pΘ τ o sτ
  g = fst (good pΘ)

  Pull : Ctx → Sub → Set
  Pull Θ' ρ = ∀ c → lookup Θ' c ≡ just ⋆ →
              P (vi (lookupₛ ρ c)) ≡ P (vi (lookupₛ ρ 0)) ++ pp Θ' (ρ ∘ τ) c

  -- The offset of a sub-coherence's first object.
  off : Sub → Nat
  off ρ = ∣ P (vi (lookupₛ ρ 0)) ∣ + o

  mutual
    comm-tm : ∀ t {B} → Θ ⊢tm t ∶ B → NS B → liftN (t [ τ ]tm) (∣ P (o₀Ty B) ∣ + o) ≡ t [ L ]tm
    comm-tm (var j) {arr B s t} (var-wf _ lj) _ =
      sym (trans (fst (snd (E j) lj)) (cong (λ q → liftN (lookupₛ τ j) (∣ q ∣ + o)) (snd (snd (E j) lj))))
    comm-tm (coh Θ' (arr A' s' t') ρ) (coh-wf (ps p₀) w' a ok sρ) _ =
      cong (coh Θ' A'') (trans (cong (liftSN Θ' (ρ ∘ τ)) oeq) (fst cs))
      where
      A'' = arr A' s' t'
      cs = commS p₀ w' ρ sρ
      T' : Nat → List Nat
      T' y = P (vi (lookupₛ ρ y))
      bd = fst (bdry T' (ps p₀) (fst (good p₀)) (monoS P g (mono-pp {Θ} {τ} pe) ρ sρ w') A' s' t' a ok 0 (ps-0 p₀))
      pl = snd cs (o₀Ty A'') (o₀-obj A'' a tt)
      q0 : pp Θ' (ρ ∘ τ) (o₀Ty A'') ≡ []
      q0 = ⊑-self (P (vi (lookupₛ ρ 0))) _ (subst (_⊑ T' 0) pl bd)
      oeq : ∣ P (o₀Ty (A'' [ ρ ]ty)) ∣ + o ≡ off ρ
      oeq = cong (λ m → ∣ P m ∣ + o)
              (trans (o₀-sub A'' ρ a tt) refl)
            ⟨≡⟩ cong (λ q → ∣ q ∣ + o) (trans pl (trans (cong (P (vi (lookupₛ ρ 0)) ++_) q0) (++-[] _)))
        where
        _⟨≡⟩_ : ∀ {a b c : Nat} → a ≡ b → b ≡ c → a ≡ c
        _⟨≡⟩_ = trans
    comm-tm (cst ()) _ _

    commS : ∀ {Θ' x' A'} → Θ' ⊢ps x' ∶ A' → Θ' ⊢ctx → ∀ ρ → Θ ⊢sub ρ ∶ Θ' →
            (liftSN Θ' (ρ ∘ τ) (off ρ) ≡ ρ ∘ L) × Pull Θ' ρ
    commS p w ⟨⟩ (⟨⟩-wf _) = refl , λ c ()
    commS p w (⟨⟩ ,ₛ r) (,-wf (⟨⟩-wf _) dr) with ps-one p
    ... | refl with ⋆-var dr refl
    ...   | m , refl with dr
    ...     | var-wf _ lm =
      cong (⟨⟩ ,ₛ_) (sym (fst (E m) lm)) ,
      λ c lc → pull0 c lc
      where
      pull0 : ∀ c → lookup (ε ▸ ⋆) c ≡ just ⋆ →
              P (vi (lookupₛ (⟨⟩ ,ₛ var m) c)) ≡ P m ++ pp (ε ▸ ⋆) ((⟨⟩ ,ₛ var m) ∘ τ) c
      pull0 c lc with lookup-cases ε ⋆ c lc
      ... | inj₁ (refl , _) = sym (++-[] (P m))
      ... | inj₂ (() , _)
    commS p (▸-wf (▸-wf w₀ bB) bC) (ρ ,ₛ ry ,ₛ rf) (,-wf (,-wf sρ dry) drf) with ps-inv p
    ... | x' , p' , refl = commS-step _ p' w₀ bB bC ρ ry rf sρ dry drf (commS p' w₀ ρ sρ)

    commS-step : ∀ B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → Θ₀ ⊢ctx → Θ₀ ⊢ty B →
                 Θ₀ ▸ B ⊢ty arr B (var x') (var (len Θ₀)) → ∀ ρ ry rf → Θ ⊢sub ρ ∶ Θ₀ →
                 Θ ⊢tm ry ∶ B [ ρ ]ty → Θ ⊢tm rf ∶ arr B (var x') (var (len Θ₀)) [ ρ ,ₛ ry ]ty →
                 (liftSN Θ₀ (ρ ∘ τ) (off ρ) ≡ ρ ∘ L) × Pull Θ₀ ρ →
                 (liftSN (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) ((ρ ,ₛ ry ,ₛ rf) ∘ τ) (off (ρ ,ₛ ry ,ₛ rf))
                    ≡ (ρ ,ₛ ry ,ₛ rf) ∘ L) ×
                 Pull (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (ρ ,ₛ ry ,ₛ rf)
    commS-step ⋆ {Θ₀} {x'} p' w₀ bB bC ρ ry rf sρ dry drf (ih , pull)
      with ⋆-var dry refl | ⋆-var (S.lookup-sub closed w₀ (snd (good p')) sρ) refl
    ... | my , refl | mx , emx = part1 , part2
      where
      n   = len Θ₀
      lρ  = sub-len' sρ
      0<n : 0 < n
      0<n = lookup-< {Θ₀} (ps-0 p')
      x<n : x' < n
      x<n = lookup-< {Θ₀} (snd (good p'))
      ρ'  = ρ ,ₛ var my ,ₛ rf
      C   = arr ⋆ (var x') (var n)
      P₀  = pp Θ₀ (ρ ∘ τ)
      lmy : lookup Θ my ≡ just ⋆
      lmy = var-obj dry
      r0eq : lookupₛ ρ' 0 ≡ lookupₛ ρ 0
      r0eq = lk-old2 ρ (var my) rf lρ 0<n
      offeq : off ρ' ≡ off ρ
      offeq = cong (λ t → ∣ P (vi t) ∣ + o) r0eq
      tyrf : C [ ρ ,ₛ var my ]ty ≡ arr ⋆ (var mx) (var my)
      tyrf = cong₂ (arr ⋆) (trans (lk₁-old {y = var my} sρ x<n) emx)
                           (lookupₛ-here ρ (var my) n (sym lρ))
      drf' : Θ ⊢tm rf ∶ arr ⋆ (var mx) (var my)
      drf' = subst (Θ ⊢tm rf ∶_) tyrf drf
      dP : P my ≡ P mx ++ path (rf [ τ ]tm)
      dP = D' pe sτ rf drf refl'
        where refl' = tyrf
      pl : P mx ≡ P (vi (lookupₛ ρ 0)) ++ P₀ x'
      pl = trans (cong (λ t → P (vi t)) (sym emx)) (pull x' (snd (good p')))
      k₁ : ∣ P mx ∣ + o ≡ ∣ P₀ x' ∣ + off ρ'
      k₁ = trans (cong (λ q → ∣ q ∣ + o) pl)
             (trans (∣++∣+ (P (vi (lookupₛ ρ 0))) (P₀ x') o) (cong (∣ P₀ x' ∣ +_) (sym offeq)))
      part1 : liftSN (Θ₀ ▸ ⋆ ▸ C) (ρ' ∘ τ) (off ρ') ≡ ρ' ∘ L
      part1 =
        cong₃ (λ a b c → a ,ₛ b ,ₛ c)
          (trans (cong (liftSN Θ₀ (ρ ∘ τ)) offeq) ih)
          (trans (cong (λ m → var (vtx (∣ path (rf [ τ ]tm) ∣ + m))) (sym k₁))
            (trans (cong (λ m → var (vtx m))
                     (sym (trans (cong (λ q → ∣ q ∣ + o) dP) (∣++∣+ (P mx) (path (rf [ τ ]tm)) o))))
                   (sym (fst (E my) lmy))))
          (trans (cong (liftN (rf [ τ ]tm)) (sym k₁)) (comm-tm rf drf' tt))
      part2 : Pull (Θ₀ ▸ ⋆ ▸ C) ρ'
      part2 c lc with lookup-cases (Θ₀ ▸ ⋆) C c lc
      ... | inj₁ (_ , ())
      ... | inj₂ (_ , lc') with lookup-cases Θ₀ ⋆ c lc'
      ...   | inj₁ (refl , _) =
              trans (cong (λ t → P (vi t)) (lk-mid2 ρ (var my) rf lρ))
               (trans dP
                (trans (cong (_++ path (rf [ τ ]tm)) pl)
                 (trans (++-assoc (P (vi (lookupₛ ρ 0))) (P₀ x') (path (rf [ τ ]tm)))
                  (cong₂ (λ t q → P (vi t) ++ q) (sym r0eq)
                         (sym (upd-n P₀ n (P₀ x' ++ path (rf [ τ ]tm)) (P₀ x')))))))
      ...   | inj₂ (c< , lc'') =
              trans (cong (λ t → P (vi t)) (lk-old2 ρ (var my) rf lρ c<))
               (trans (pull c lc'')
                (cong₂ (λ t q → P (vi t) ++ q) (sym r0eq)
                       (sym (upd-old P₀ n (P₀ x' ++ path (rf [ τ ]tm)) (P₀ x') c c<))))
    commS-step (arr B₀ s₀ t₀) {Θ₀} {x'} p' w₀ bB bC ρ ry rf sρ dry drf (ih , pull) = part1 , part2
      where
      n   = len Θ₀
      lρ  = sub-len' sρ
      B   = arr B₀ s₀ t₀
      C   = arr B (var x') (var n)
      0<n : 0 < n
      0<n = lookup-< {Θ₀} (ps-0 p')
      lx  = snd (good p')
      ρ'  = ρ ,ₛ ry ,ₛ rf
      P₀  = pp Θ₀ (ρ ∘ τ)
      r0eq : lookupₛ ρ' 0 ≡ lookupₛ ρ 0
      r0eq = lk-old2 ρ ry rf lρ 0<n
      offeq : off ρ' ≡ off ρ
      offeq = cong (λ t → ∣ P (vi t) ∣ + o) r0eq
      ob : lookup Θ₀ (o₀Ty B) ≡ just ⋆
      ob = o₀-obj B bB tt
      o<n : o₀Ty B < n
      o<n = lookup-< {Θ₀} ob
      eB : o₀Ty (B [ ρ ]ty) ≡ vi (lookupₛ ρ (o₀Ty B))
      eB = o₀-sub B ρ bB tt
      eC : o₀Ty (C [ ρ ,ₛ ry ]ty) ≡ o₀Ty (B [ ρ ]ty)
      eC = trans (o₀-sub C (ρ ,ₛ ry) bC tt) (trans (cong vi (lk₁-old {y = ry} sρ o<n)) (sym eB))
      xo : P₀ x' ≡ P₀ (o₀Ty B)
      xo = snd (snd (ent p' (ρ ∘ τ) o (sub∘ w₀ sρ sτ) x') lx)
      k₂ : ∣ P (o₀Ty (B [ ρ ]ty)) ∣ + o ≡ ∣ P₀ x' ∣ + off ρ'
      k₂ = trans (cong (λ m → ∣ P m ∣ + o) eB)
            (trans (cong (λ q → ∣ q ∣ + o) (pull (o₀Ty B) ob))
             (trans (∣++∣+ (P (vi (lookupₛ ρ 0))) (P₀ (o₀Ty B)) o)
                    (cong₂ (λ q m → ∣ q ∣ + m) (sym xo) (sym offeq))))
      k₃ : ∣ P (o₀Ty (C [ ρ ,ₛ ry ]ty)) ∣ + o ≡ ∣ P₀ x' ∣ + off ρ'
      k₃ = trans (cong (λ m → ∣ P m ∣ + o) eC) k₂
      part1 : liftSN (Θ₀ ▸ B ▸ C) (ρ' ∘ τ) (off ρ') ≡ ρ' ∘ L
      part1 =
        cong₃ (λ a b c → a ,ₛ b ,ₛ c)
          (trans (cong (liftSN Θ₀ (ρ ∘ τ)) offeq) ih)
          (trans (cong (liftN (ry [ τ ]tm)) (sym k₂)) (comm-tm ry dry tt))
          (trans (cong (liftN (rf [ τ ]tm)) (sym k₃)) (comm-tm rf drf tt))
      part2 : Pull (Θ₀ ▸ B ▸ C) ρ'
      part2 c lc with lookup-cases (Θ₀ ▸ B) C c lc
      ... | inj₁ (_ , ())
      ... | inj₂ (_ , lc') with lookup-cases Θ₀ B c lc'
      ...   | inj₁ (_ , ())
      ...   | inj₂ (c< , lc'') =
              trans (cong (λ t → P (vi t)) (lk-old2 ρ ry rf lρ c<))
               (trans (pull c lc'')
                (cong₂ (λ t q → P (vi t) ++ q) (sym r0eq)
                       (sym (upd-old P₀ n (P₀ x') (P₀ x') c c<))))

  comm-ty : ∀ B → Θ ⊢ty B → NS B →
            liftTy (B [ τ ]ty) (∣ P (o₀Ty B) ∣ + o) (∣ P (o₁Ty B) ∣ + o) ≡ B [ L ]ty
  comm-ty (arr ⋆ a b) (arr-wf da db) _ with ⋆-var da refl | ⋆-var db refl
  ... | c , refl | d , refl = cong₂ (arr ⋆) (sym (fst (E c) (var-obj da))) (sym (fst (E d) (var-obj db)))
  comm-ty (arr (arr B' s₀ t₀) a b) (arr-wf da db) _ =
    cong₃ arr (comm-ty (arr B' s₀ t₀) (tm-ty da) tt) (comm-tm a da tt) (comm-tm b db tt)

------------------------------------------------------------------------
-- The lift is well typed.

private
  ⊑-nil : ∀ p → p ⊑ [] → p ≡ []
  ⊑-nil []      _       = refl
  ⊑-nil (x ∷ p) (r , ())

  ⊑-len : ∀ {p q} → p ⊑ q → ∣ p ∣ ≤ ∣ q ∣
  ⊑-len {p} (r , refl) = subst (∣ p ∣ ≤_) (sym (∣++∣ p r)) (≤-+r ∣ p ∣ ∣ r ∣)
    where
    ≤-+r : ∀ m n → m ≤ m + n
    ≤-+r zero    n = z≤n
    ≤-+r (suc m) n = s≤s (≤-+r m n)

  +-mono-l : ∀ {m n} k → m ≤ n → m + k ≤ n + k
  +-mono-l {m} {n} k h = subst₂' (+-comm k m) (+-comm k n) (+-mono-≤ k h)
    where
    subst₂' : ∀ {a b c d} → a ≡ b → c ≡ d → a ≤ c → b ≤ d
    subst₂' refl refl h = h

  ext-ty' : ∀ {Γ Θ σ s B} → Γ ⊢sub σ ∶ Θ → Θ ⊢ty B → B [ σ ,ₛ s ]ty ≡ B [ σ ]ty
  ext-ty' {σ = σ} {s} {B} sσ b =
    S.ext-ty B σ s (subst (λ n → S.ScTy n B) (sym (sub-len' sσ)) (S.ty-sc closed b))

-- The boundary of a valid coherence, for positions.
module Bd {Γ Θ x₀} (τ : Sub) (sτ : Γ ⊢sub τ ∶ Θ) (p₀ : Θ ⊢ps x₀ ∶ ⋆) (pe : PEdge Θ τ)
          (A' : Ty) (s' t' : Tm) (a : Θ ⊢ty arr A' s' t') (ok : T (cattSide Θ A' s' t')) where
  bd : ∀ c → lookup Θ c ≡ just ⋆ → (pp Θ τ (o₀Ty (arr A' s' t')) ⊑ pp Θ τ c) × (pp Θ τ c ⊑ pp Θ τ (o₁Ty (arr A' s' t')))
  bd = bdry (pp Θ τ) (ps p₀) (fst (good p₀)) (mono-pp {Θ} {τ} pe) A' s' t' a ok

  start : pp Θ τ (o₀Ty (arr A' s' t')) ≡ []
  start = ⊑-nil _ (subst (pp Θ τ (o₀Ty (arr A' s' t')) ⊑_) (pp-0 p₀ τ sτ) (fst (bd 0 (ps-0 p₀))))

-- The path of a coherence's 1-dimensional source ends at the position
-- of its last object.
coh-len : ∀ {Γ Θ x₀ A' s' t' τ} → Γ ⊢sub τ ∶ Θ → (p₀ : Θ ⊢ps x₀ ∶ ⋆) → (pe : PEdge Θ τ) →
          (a : Θ ⊢ty arr A' s' t') → (ok : T (cattSide Θ A' s' t')) →
          pp Θ τ (o₁Ty (arr A' s' t')) ≡ π (arr A' s' t' [ τ ]ty) (coh Θ (arr A' s' t') τ)
coh-len {A' = ⋆} {τ = τ} sτ p₀ pe (arr-wf ds dt) ok with ⋆-var ds refl | ⋆-var dt refl
... | j , refl | j' , refl with chain-side (ps p₀) ok
...   | k , refl , refl , refl = pp-chain k τ sτ
coh-len {A' = arr X u v} {s'} {t'} {τ} sτ p₀ pe a@(arr-wf ds dt) ok =
  trans (πty pe sτ (arr X u v) s' ds tt) (cong (_++ π (arr X u v [ τ ]ty) (s' [ τ ]tm)) start)
  where open Bd τ sτ p₀ pe (arr X u v) s' t' a ok

mutual
  liftN-ty : ∀ {Γ K} → Graph Γ → ∀ t {A} o → Γ ⊢tm t ∶ A → NS A → ∣ π A t ∣ + o ≤ K →
             chainC K ⊢tm liftN t o ∶ liftTy A o (∣ π A t ∣ + o)
  liftN-ty gr (var i) {arr ⋆ a b} o d _ le = lift-ty (var i) o d refl le
  liftN-ty gr (var i) {arr (arr _ _ _) _ _} o (var-wf _ eq) _ le = ⊥-elim (gr i eq)
  liftN-ty {Γ} {K} gr (coh Θ (arr A' s' t') τ) o (coh-wf (ps p₀) w a ok sτ) _ le =
    subst (chainC K ⊢tm coh Θ A'' (liftSN Θ τ o) ∶_) tyEq (coh-wf (ps p₀) w a ok sL)
    where
    A'' = arr A' s' t'
    pe  = pedge gr p₀ τ sτ
    open Bd τ sτ p₀ pe A' s' t' a ok
    cl  = coh-len sτ p₀ pe a ok
    πℓ  = ∣ π (A'' [ τ ]ty) (coh Θ A'' τ) ∣
    bnd : ∀ c → lookup Θ c ≡ just ⋆ → ∣ pp Θ τ c ∣ + o ≤ K
    bnd c lc = ≤-trans (+-mono-l o (subst (∣ pp Θ τ c ∣ ≤_) (cong ∣_∣ cl) (⊑-len (snd (bd c lc))))) le
    sL : chainC K ⊢sub liftSN Θ τ o ∶ Θ
    sL = liftSN-ty gr p₀ w τ o sτ bnd
    tyEq : A'' [ liftSN Θ τ o ]ty ≡ liftTy (A'' [ τ ]ty) o (πℓ + o)
    tyEq = sym (trans (cong₂ (liftTy (A'' [ τ ]ty)) (cong (λ q → ∣ q ∣ + o) (sym start))
                                                   (cong (λ q → ∣ q ∣ + o) (sym cl)))
                      (Comm.comm-ty τ o sτ p₀ w pe A'' a tt))
  liftN-ty gr (cst ()) _ _ _ _

  liftSN-ty : ∀ {Γ K Θ x A} → Graph Γ → Θ ⊢ps x ∶ A → Θ ⊢ctx → ∀ τ o → Γ ⊢sub τ ∶ Θ →
              (∀ c → lookup Θ c ≡ just ⋆ → ∣ pp Θ τ c ∣ + o ≤ K) → chainC K ⊢sub liftSN Θ τ o ∶ Θ
  liftSN-ty {K = K} gr p w ⟨⟩ o (⟨⟩-wf _) bnd = ⟨⟩-wf (chainC-wf K)
  liftSN-ty {K = K} gr p w (⟨⟩ ,ₛ a) o (,-wf (⟨⟩-wf _) _) bnd with ps-one p
  ... | refl = ,-wf (⟨⟩-wf (chainC-wf K)) (var-wf (chainC-wf K) (lookup-vtx K o (bnd 0 refl)))
  liftSN-ty gr p w@(▸-wf (▸-wf w₀ bB) bC) (τ₀ ,ₛ y ,ₛ f) o s@(,-wf (,-wf sτ₀ dy) df) bnd with ps-inv p
  ... | x' , p' , refl = liftSN-ty-step gr _ p' w₀ bB bC w τ₀ y f o sτ₀ dy df s bnd

  liftSN-ty-step : ∀ {Γ K} → Graph Γ → ∀ B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → Θ₀ ⊢ctx → Θ₀ ⊢ty B →
                   (Θ₀ ▸ B) ⊢ty arr B (var x') (var (len Θ₀)) →
                   (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) ⊢ctx → ∀ τ₀ y f o → Γ ⊢sub τ₀ ∶ Θ₀ →
                   Γ ⊢tm y ∶ B [ τ₀ ]ty → Γ ⊢tm f ∶ arr B (var x') (var (len Θ₀)) [ τ₀ ,ₛ y ]ty →
                   Γ ⊢sub τ₀ ,ₛ y ,ₛ f ∶ Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀)) →
                   (∀ c → lookup (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) c ≡ just ⋆ →
                      ∣ pp (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ₀ ,ₛ y ,ₛ f) c ∣ + o ≤ K) →
                   chainC K ⊢sub liftSN (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ₀ ,ₛ y ,ₛ f) o
                                 ∶ Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))
  liftSN-ty-step {Γ} {K} gr ⋆ {Θ₀} {x'} p' w₀ bB bC wF τ₀ y f o sτ₀ dy df sF bnd =
    ,-wf (,-wf ih dy') df'
    where
    n   = len Θ₀
    C   = arr ⋆ (var x') (var n)
    P₀  = pp Θ₀ τ₀
    L₀  = liftSN Θ₀ τ₀ o
    ox  = ∣ P₀ x' ∣ + o
    wK  = chainC-wf K
    lx  = snd (good p')
    x<n : x' < n
    x<n = lookup-< {Θ₀} lx
    lL  = lenL p' τ₀ o sτ₀
    bnd₀ : ∀ c → lookup Θ₀ c ≡ just ⋆ → ∣ P₀ c ∣ + o ≤ K
    bnd₀ c lc = subst (λ q → ∣ q ∣ + o ≤ K) (upd-old P₀ n (P₀ x' ++ path f) (P₀ x') c (lookup-< {Θ₀} lc))
                      (bnd c (lookup-wk {Θ₀ ▸ ⋆} {C} (lookup-wk {Θ₀} {⋆} lc)))
    ih : chainC K ⊢sub L₀ ∶ Θ₀
    ih = liftSN-ty gr p' w₀ τ₀ o sτ₀ bnd₀
    bn : ∣ path f ∣ + ox ≤ K
    bn = subst (_≤ K) (trans (cong (λ q → ∣ q ∣ + o) (upd-n P₀ n (P₀ x' ++ path f) (P₀ x')))
                             (∣++∣+ (P₀ x') (path f) o))
               (bnd n (lookup-wk {Θ₀ ▸ ⋆} {C} (lookup-here Θ₀ ⋆ n refl)))
    y'  = var (vtx (∣ path f ∣ + ox))
    dy' : chainC K ⊢tm y' ∶ ⋆
    dy' = var-wf wK (lookup-vtx K _ bn)
    eqf : arr ⋆ (var (vtx ox)) (var (vtx (∣ path f ∣ + ox))) ≡ C [ L₀ ,ₛ y' ]ty
    eqf = cong₂ (arr ⋆)
            (sym (trans (lookupₛ-there L₀ y' x' (subst (x' <_) (sym lL) x<n)) (fst (ent p' τ₀ o sτ₀ x') lx)))
            (sym (lookupₛ-here L₀ y' n (sym lL)))
    df' : chainC K ⊢tm liftN f ox ∶ C [ L₀ ,ₛ y' ]ty
    df' = subst (chainC K ⊢tm liftN f ox ∶_) eqf (liftN-ty gr f ox df tt bn)
  liftSN-ty-step {Γ} {K} gr (arr B₀ s₀ t₀) {Θ₀} {x'} p' w₀ bB bC wF τ₀ y f o sτ₀ dy df sF bnd =
    ,-wf (,-wf ih dy') df'
    where
    n   = len Θ₀
    B   = arr B₀ s₀ t₀
    C   = arr B (var x') (var n)
    P₀  = pp Θ₀ τ₀
    L₀  = liftSN Θ₀ τ₀ o
    ox  = ∣ P₀ x' ∣ + o
    lx  = snd (good p')
    x<n : x' < n
    x<n = lookup-< {Θ₀} lx
    lL  = lenL p' τ₀ o sτ₀
    lτ  = sub-len' sτ₀
    E₀  = ent p' τ₀ o sτ₀
    pe₀ = pedge gr p' τ₀ sτ₀
    bnd₀ : ∀ c → lookup Θ₀ c ≡ just ⋆ → ∣ P₀ c ∣ + o ≤ K
    bnd₀ c lc = subst (λ q → ∣ q ∣ + o ≤ K) (upd-old P₀ n (P₀ x') (P₀ x') c (lookup-< {Θ₀} lc))
                      (bnd c (lookup-wk {Θ₀ ▸ B} {C} (lookup-wk {Θ₀} {B} lc)))
    ih : chainC K ⊢sub L₀ ∶ Θ₀
    ih = liftSN-ty gr p' w₀ τ₀ o sτ₀ bnd₀
    xo : P₀ x' ≡ P₀ (o₀Ty B)
    xo = snd (snd (E₀ x') lx)
    o₀<n : o₀Ty B < n
    o₀<n = lookup-< {Θ₀} (o₀-obj B bB tt)
    o₁<n : o₁Ty B < n
    o₁<n = lookup-< {Θ₀} (o₁-obj B bB tt)
    bB' : (Θ₀ ▸ B) ⊢ty B
    bB' = wk-ty bB (▸-wf w₀ bB)
    eBy : B [ τ₀ ,ₛ y ]ty ≡ B [ τ₀ ]ty
    eBy = ext-ty' sτ₀ bB
    eBτ : B [ τ₀ ,ₛ y ,ₛ f ]ty ≡ B [ τ₀ ]ty
    eBτ = trans (ext-ty' (,-wf sτ₀ dy) bB') eBy
    -- The path of y, via the full context.
    PF  = pp (Θ₀ ▸ B ▸ C) (τ₀ ,ₛ y ,ₛ f)
    πyF : PF (o₁Ty B) ≡ PF (o₀Ty B) ++ π (B [ τ₀ ,ₛ y ,ₛ f ]ty) (lookupₛ (τ₀ ,ₛ y ,ₛ f) n)
    πyF = πty (pedge gr (pse p') (τ₀ ,ₛ y ,ₛ f) sF) sF B (var n)
              (var-wf wF (lookup-wk {Θ₀ ▸ B} {C} (lookup-here Θ₀ B n refl))) tt
    πy : P₀ (o₁Ty B) ≡ P₀ (o₀Ty B) ++ π (B [ τ₀ ]ty) y
    πy = trans (sym (upd-old P₀ n (P₀ x') (P₀ x') _ o₁<n))
          (trans πyF (cong₂ _++_ (upd-old P₀ n (P₀ x') (P₀ x') _ o₀<n)
                                 (cong₂ π eBτ (lk-mid2 τ₀ y f lτ))))
    πx : P₀ (o₁Ty B) ≡ P₀ (o₀Ty B) ++ π (B [ τ₀ ]ty) (lookupₛ τ₀ x')
    πx = πty pe₀ sτ₀ B (var x') (var-wf w₀ lx) tt
    -- Offsets.
    len-y : ∣ π (B [ τ₀ ]ty) y ∣ + ox ≡ ∣ P₀ (o₁Ty B) ∣ + o
    len-y = trans (cong (λ q → ∣ π (B [ τ₀ ]ty) y ∣ + (∣ q ∣ + o)) xo)
             (trans (sym (∣++∣+ (P₀ (o₀Ty B)) (π (B [ τ₀ ]ty) y) o)) (cong (λ q → ∣ q ∣ + o) (sym πy)))
    len-x : ∣ π (B [ τ₀ ]ty) (lookupₛ τ₀ x') ∣ + ox ≡ ∣ P₀ (o₁Ty B) ∣ + o
    len-x = trans (cong (λ q → ∣ π (B [ τ₀ ]ty) (lookupₛ τ₀ x') ∣ + (∣ q ∣ + o)) xo)
             (trans (sym (∣++∣+ (P₀ (o₀Ty B)) (π (B [ τ₀ ]ty) (lookupₛ τ₀ x')) o))
                    (cong (λ q → ∣ q ∣ + o) (sym πx)))
    ox-eq : ox ≡ ∣ P₀ (o₀Ty B) ∣ + o
    ox-eq = cong (λ q → ∣ q ∣ + o) xo
    commB : liftTy (B [ τ₀ ]ty) (∣ P₀ (o₀Ty B) ∣ + o) (∣ P₀ (o₁Ty B) ∣ + o) ≡ B [ L₀ ]ty
    commB = Comm.comm-ty τ₀ o sτ₀ p' w₀ pe₀ B bB tt
    bo₁ : ∣ P₀ (o₁Ty B) ∣ + o ≤ K
    bo₁ = bnd₀ (o₁Ty B) (o₁-obj B bB tt)
    -- y.
    y'  = liftN y ox
    dy' : chainC K ⊢tm y' ∶ B [ L₀ ]ty
    dy' = subst (chainC K ⊢tm y' ∶_) (trans (cong₂ (liftTy (B [ τ₀ ]ty)) ox-eq len-y) commB)
                (liftN-ty gr y ox dy tt (subst (_≤ K) (sym len-y) bo₁))
    -- f.
    eu : lookupₛ (τ₀ ,ₛ y) x' ≡ lookupₛ τ₀ x'
    eu = lk₁-old {y = y} sτ₀ x<n
    πf : π (B [ τ₀ ,ₛ y ]ty) (lookupₛ (τ₀ ,ₛ y) x') ≡ π (B [ τ₀ ]ty) (lookupₛ τ₀ x')
    πf = cong₂ π eBy eu
    bnf : ∣ π (C [ τ₀ ,ₛ y ]ty) f ∣ + ox ≤ K
    bnf = subst (_≤ K) (sym (trans (cong (λ q → ∣ q ∣ + ox) πf) len-x)) bo₁
    e1 : liftTy (B [ τ₀ ,ₛ y ]ty) ox (∣ π (B [ τ₀ ,ₛ y ]ty) (lookupₛ (τ₀ ,ₛ y) x') ∣ + ox)
         ≡ B [ L₀ ,ₛ y' ]ty
    e1 = trans (cong₂ (λ X q → liftTy X ox (∣ q ∣ + ox)) eBy πf)
          (trans (cong₂ (liftTy (B [ τ₀ ]ty)) ox-eq len-x)
           (trans commB (sym (ext-ty' ih bB))))
    e2 : liftN (lookupₛ (τ₀ ,ₛ y) x') ox ≡ lookupₛ (L₀ ,ₛ y') x'
    e2 = trans (cong (λ t → liftN t ox) eu)
          (trans (sym (fst (snd (E₀ x') lx))) (sym (lookupₛ-there L₀ y' x' (subst (x' <_) (sym lL) x<n))))
    e3 : liftN (lookupₛ (τ₀ ,ₛ y) n) ox ≡ lookupₛ (L₀ ,ₛ y') n
    e3 = trans (cong (λ t → liftN t ox) (lookupₛ-here τ₀ y n (sym lτ)))
               (sym (lookupₛ-here L₀ y' n (sym lL)))
    df' : chainC K ⊢tm liftN f ox ∶ C [ L₀ ,ₛ y' ]ty
    df' = subst (chainC K ⊢tm liftN f ox ∶_) (cong₃ arr e1 e2 e3) (liftN-ty gr f ox df tt bnf)

------------------------------------------------------------------------
-- Substituting the walk back into the lift gives the original cell.

private
  seg-pre : ∀ {Γ σ o x p Q} → Seg Γ σ o x Q → p ⊑ Q → Seg Γ σ o x p
  seg-pre {Γ} {σ} {o} {x} {p} sg (r , refl) = fst (seg-split p r sg)

  seg-mid : ∀ {Γ σ o x p q Q} → Seg Γ σ o x Q → p ++ q ⊑ Q → Seg Γ σ (∣ p ∣ + o) (endOf Γ x p) q
  seg-mid {Γ} {σ} {o} {x} {p} {q} sg h = snd (seg-split p q (seg-pre sg h))

  walk-nil : ∀ {Γ x y} → Walk Γ x [] y → x ≡ y
  walk-nil nil = refl

mutual
  liftN-sub : ∀ {Γ} → Graph Γ → ∀ t {A} o → Γ ⊢tm t ∶ A → NS A → ∀ {σ} →
              Seg Γ σ o (o₀Ty A) (π A t) → liftN t o [ σ ]tm ≡ t
  liftN-sub gr (var i) {arr ⋆ a b} o d _ (_ , he , _) = he
  liftN-sub gr (var i) {arr (arr _ _ _) _ _} o (var-wf _ eq) _ _ = ⊥-elim (gr i eq)
  liftN-sub {Γ} gr (coh Θ (arr A' s' t') τ) o (coh-wf (ps p₀) w a ok sτ) _ {σ} sg =
    cong (coh Θ A'') (liftSN-sub gr p₀ w τ o sτ sg' (λ c lc → snd (bd c lc)))
    where
    A'' = arr A' s' t'
    pe  = pedge gr p₀ τ sτ
    open Bd τ sτ p₀ pe A' s' t' a ok
    cl  = coh-len sτ p₀ pe a ok
    x0 : o₀Ty (A'' [ τ ]ty) ≡ vi (lookupₛ τ 0)
    x0 = trans (o₀-sub A'' τ a tt)
           (sym (walk-nil (subst (λ q → Walk Γ (vi (lookupₛ τ 0)) q (vi (lookupₛ τ (o₀Ty A''))))
                                 start (walkpp p₀ w τ sτ (o₀Ty A'') (o₀-obj A'' a tt)))))
    sg' : Seg Γ σ o (vi (lookupₛ τ 0)) (pp Θ τ (o₁Ty A''))
    sg' = subst₂ (Seg Γ σ o) x0 (sym cl) sg
      where
      subst₂ : ∀ {A B : Set} (R : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → R a b → R a' b'
      subst₂ R refl refl r = r
  liftN-sub gr (cst ()) _ _ _ _

  liftSN-sub : ∀ {Γ Θ x A} → Graph Γ → Θ ⊢ps x ∶ A → Θ ⊢ctx → ∀ τ o → Γ ⊢sub τ ∶ Θ → ∀ {σ Q} →
               Seg Γ σ o (vi (lookupₛ τ 0)) Q → (∀ c → lookup Θ c ≡ just ⋆ → pp Θ τ c ⊑ Q) →
               liftSN Θ τ o ∘ σ ≡ τ
  liftSN-sub gr p w ⟨⟩ o (⟨⟩-wf _) sg bq = refl
  liftSN-sub gr p w (⟨⟩ ,ₛ a) o (,-wf (⟨⟩-wf _) da) {Q = Q} sg bq with ps-one p
  ... | refl with ⋆-var da refl
  ...   | m , refl = cong (⟨⟩ ,ₛ_) (seg-head Q sg)
  liftSN-sub gr p w@(▸-wf (▸-wf w₀ bB) bC) (τ₀ ,ₛ y ,ₛ f) o s@(,-wf (,-wf sτ₀ dy) df) sg bq with ps-inv p
  ... | x' , p' , refl = liftSN-sub-step gr _ p' w₀ bB bC w τ₀ y f o sτ₀ dy df s sg bq

  liftSN-sub-step : ∀ {Γ} → Graph Γ → ∀ B {Θ₀ x'} → Θ₀ ⊢ps x' ∶ B → Θ₀ ⊢ctx → Θ₀ ⊢ty B →
                    (Θ₀ ▸ B) ⊢ty arr B (var x') (var (len Θ₀)) →
                    (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) ⊢ctx → ∀ τ₀ y f o → Γ ⊢sub τ₀ ∶ Θ₀ →
                    Γ ⊢tm y ∶ B [ τ₀ ]ty → Γ ⊢tm f ∶ arr B (var x') (var (len Θ₀)) [ τ₀ ,ₛ y ]ty →
                    Γ ⊢sub τ₀ ,ₛ y ,ₛ f ∶ Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀)) → ∀ {σ Q} →
                    Seg Γ σ o (vi (lookupₛ (τ₀ ,ₛ y ,ₛ f) 0)) Q →
                    (∀ c → lookup (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) c ≡ just ⋆ →
                       pp (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ₀ ,ₛ y ,ₛ f) c ⊑ Q) →
                    liftSN (Θ₀ ▸ B ▸ arr B (var x') (var (len Θ₀))) (τ₀ ,ₛ y ,ₛ f) o ∘ σ ≡ τ₀ ,ₛ y ,ₛ f
  liftSN-sub-step {Γ} gr ⋆ {Θ₀} {x'} p' w₀ bB bC wF τ₀ y f o sτ₀ dy df sF {σ} {Q} sg bq
    with ⋆-var dy refl
  ... | z , refl =
    cong₃ (λ a b c → a ,ₛ b ,ₛ c) ih objEq (liftN-sub gr f ox df tt sgf)
    where
    n   = len Θ₀
    C   = arr ⋆ (var x') (var n)
    P₀  = pp Θ₀ τ₀
    ox  = ∣ P₀ x' ∣ + o
    lx  = snd (good p')
    x<n : x' < n
    x<n = lookup-< {Θ₀} lx
    lτ  = sub-len' sτ₀
    0<n : 0 < n
    0<n = lookup-< {Θ₀} (ps-0 p')
    x0  : vi (lookupₛ (τ₀ ,ₛ var z ,ₛ f) 0) ≡ vi (lookupₛ τ₀ 0)
    x0  = cong vi (lk-old2 τ₀ (var z) f lτ 0<n)
    sg₀ : Seg Γ σ o (vi (lookupₛ τ₀ 0)) Q
    sg₀ = subst (λ t → Seg Γ σ o t Q) x0 sg
    bq₀ : ∀ c → lookup Θ₀ c ≡ just ⋆ → P₀ c ⊑ Q
    bq₀ c lc = subst (_⊑ Q) (upd-old P₀ n (P₀ x' ++ path f) (P₀ x') c (lookup-< {Θ₀} lc))
                     (bq c (lookup-wk {Θ₀ ▸ ⋆} {C} (lookup-wk {Θ₀} {⋆} lc)))
    ih = liftSN-sub gr p' w₀ τ₀ o sτ₀ sg₀ bq₀
    bn : P₀ x' ++ path f ⊑ Q
    bn = subst (_⊑ Q) (upd-n P₀ n (P₀ x' ++ path f) (P₀ x'))
               (bq n (lookup-wk {Θ₀ ▸ ⋆} {C} (lookup-here Θ₀ ⋆ n refl)))
    Wn : Walk Γ (vi (lookupₛ τ₀ 0)) (P₀ x' ++ path f) z
    Wn = subst₂' (λ a q → Walk Γ a q z) x0 (upd-n P₀ n (P₀ x' ++ path f) (P₀ x'))
           (subst (λ t → Walk Γ _ _ (vi t)) (lk-mid2 τ₀ (var z) f lτ)
             (walkpp (pse p') wF (τ₀ ,ₛ var z ,ₛ f) sF n (lookup-wk {Θ₀ ▸ ⋆} {C} (lookup-here Θ₀ ⋆ n refl))))
      where
      subst₂' : ∀ {A B : Set} (R : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → R a b → R a' b'
      subst₂' R refl refl r = r
    objEq : var (vtx (∣ path f ∣ + ox)) [ σ ]tm ≡ var z
    objEq = trans (cong (λ m → lookupₛ σ (vtx m)) (sym (∣++∣+ (P₀ x') (path f) o)))
             (trans (seg-end (P₀ x' ++ path f) (seg-pre sg₀ bn)) (cong var (walk-end Wn)))
    Wx : endOf Γ (vi (lookupₛ τ₀ 0)) (P₀ x') ≡ vi (lookupₛ τ₀ x')
    Wx = walk-end (walkpp p' w₀ τ₀ sτ₀ x' lx)
    sgf : Seg Γ σ ox (o₀Ty (C [ τ₀ ,ₛ var z ]ty)) (path f)
    sgf = subst (λ t → Seg Γ σ ox t (path f))
                (trans Wx (cong vi (sym (lk₁-old {y = var z} sτ₀ x<n))))
                (seg-mid sg₀ bn)
  liftSN-sub-step {Γ} gr (arr B₀ s₀ t₀) {Θ₀} {x'} p' w₀ bB bC wF τ₀ y f o sτ₀ dy df sF {σ} {Q} sg bq =
    cong₃ (λ a b c → a ,ₛ b ,ₛ c) ih (liftN-sub gr y ox dy tt sgy) (liftN-sub gr f ox df tt sgf)
    where
    n   = len Θ₀
    B   = arr B₀ s₀ t₀
    C   = arr B (var x') (var n)
    P₀  = pp Θ₀ τ₀
    ox  = ∣ P₀ x' ∣ + o
    lx  = snd (good p')
    x<n : x' < n
    x<n = lookup-< {Θ₀} lx
    lτ  = sub-len' sτ₀
    0<n : 0 < n
    0<n = lookup-< {Θ₀} (ps-0 p')
    pe₀ = pedge gr p' τ₀ sτ₀
    x0  : vi (lookupₛ (τ₀ ,ₛ y ,ₛ f) 0) ≡ vi (lookupₛ τ₀ 0)
    x0  = cong vi (lk-old2 τ₀ y f lτ 0<n)
    sg₀ : Seg Γ σ o (vi (lookupₛ τ₀ 0)) Q
    sg₀ = subst (λ t → Seg Γ σ o t Q) x0 sg
    bq₀ : ∀ c → lookup Θ₀ c ≡ just ⋆ → P₀ c ⊑ Q
    bq₀ c lc = subst (_⊑ Q) (upd-old P₀ n (P₀ x') (P₀ x') c (lookup-< {Θ₀} lc))
                     (bq c (lookup-wk {Θ₀ ▸ B} {C} (lookup-wk {Θ₀} {B} lc)))
    ih = liftSN-sub gr p' w₀ τ₀ o sτ₀ sg₀ bq₀
    xo : P₀ x' ≡ P₀ (o₀Ty B)
    xo = snd (snd (ent p' τ₀ o sτ₀ x') lx)
    ob₀ = o₀-obj B bB tt
    ob₁ = o₁-obj B bB tt
    o₀<n : o₀Ty B < n
    o₀<n = lookup-< {Θ₀} ob₀
    o₁<n : o₁Ty B < n
    o₁<n = lookup-< {Θ₀} ob₁
    bB' : (Θ₀ ▸ B) ⊢ty B
    bB' = wk-ty bB (▸-wf w₀ bB)
    eBy : B [ τ₀ ,ₛ y ]ty ≡ B [ τ₀ ]ty
    eBy = ext-ty' sτ₀ bB
    eBτ : B [ τ₀ ,ₛ y ,ₛ f ]ty ≡ B [ τ₀ ]ty
    eBτ = trans (ext-ty' (,-wf sτ₀ dy) bB') eBy
    PF  = pp (Θ₀ ▸ B ▸ C) (τ₀ ,ₛ y ,ₛ f)
    πyF : PF (o₁Ty B) ≡ PF (o₀Ty B) ++ π (B [ τ₀ ,ₛ y ,ₛ f ]ty) (lookupₛ (τ₀ ,ₛ y ,ₛ f) n)
    πyF = πty (pedge gr (pse p') (τ₀ ,ₛ y ,ₛ f) sF) sF B (var n)
              (var-wf wF (lookup-wk {Θ₀ ▸ B} {C} (lookup-here Θ₀ B n refl))) tt
    πy : P₀ (o₁Ty B) ≡ P₀ (o₀Ty B) ++ π (B [ τ₀ ]ty) y
    πy = trans (sym (upd-old P₀ n (P₀ x') (P₀ x') _ o₁<n))
          (trans πyF (cong₂ _++_ (upd-old P₀ n (P₀ x') (P₀ x') _ o₀<n)
                                 (cong₂ π eBτ (lk-mid2 τ₀ y f lτ))))
    πx : P₀ (o₁Ty B) ≡ P₀ (o₀Ty B) ++ π (B [ τ₀ ]ty) (lookupₛ τ₀ x')
    πx = πty pe₀ sτ₀ B (var x') (var-wf w₀ lx) tt
    b₁ : P₀ (o₁Ty B) ⊑ Q
    b₁ = bq₀ (o₁Ty B) ob₁
    W₀ : endOf Γ (vi (lookupₛ τ₀ 0)) (P₀ (o₀Ty B)) ≡ o₀Ty (B [ τ₀ ]ty)
    W₀ = trans (walk-end (walkpp p' w₀ τ₀ sτ₀ (o₀Ty B) ob₀)) (sym (o₀-sub B τ₀ bB tt))
    oxe : ∣ P₀ (o₀Ty B) ∣ + o ≡ ox
    oxe = cong (λ q → ∣ q ∣ + o) (sym xo)
    sgy : Seg Γ σ ox (o₀Ty (B [ τ₀ ]ty)) (π (B [ τ₀ ]ty) y)
    sgy = subst₂' (λ m t → Seg Γ σ m t (π (B [ τ₀ ]ty) y)) oxe W₀
            (seg-mid sg₀ (subst (_⊑ Q) πy b₁))
      where
      subst₂' : ∀ {A B : Set} (R : A → B → Set) {a a' b b'} → a ≡ a' → b ≡ b' → R a b → R a' b'
      subst₂' R refl refl r = r
    oC : o₀Ty (C [ τ₀ ,ₛ y ]ty) ≡ o₀Ty (B [ τ₀ ]ty)
    oC = cong o₀Ty eBy
    πC : π (C [ τ₀ ,ₛ y ]ty) f ≡ π (B [ τ₀ ]ty) (lookupₛ τ₀ x')
    πC = cong₂ π eBy (lk₁-old {y = y} sτ₀ x<n)
    sgf : Seg Γ σ ox (o₀Ty (C [ τ₀ ,ₛ y ]ty)) (π (C [ τ₀ ,ₛ y ]ty) f)
    sgf = subst₃' (λ m t q → Seg Γ σ m t q) oxe (trans W₀ (sym oC)) (sym πC)
            (seg-mid sg₀ (subst (_⊑ Q) πx b₁))
      where
      subst₃' : ∀ {A B C : Set} (R : A → B → C → Set) {a a' b b' c c'} →
                a ≡ a' → b ≡ b' → c ≡ c' → R a b c → R a' b' c'
      subst₃' R refl refl refl r = r

------------------------------------------------------------------------
-- Substituting σ back into the lifted type gives the original type.

private
  arr-l′ : ∀ {Θ A a b} → Θ ⊢ty arr A a b → Θ ⊢tm a ∶ A
  arr-l′ (arr-wf da _) = da

  arr-r′ : ∀ {Θ A a b} → Θ ⊢ty arr A a b → Θ ⊢tm b ∶ A
  arr-r′ (arr-wf _ db) = db

liftTy-sub : ∀ {Γ σ} → Graph Γ → ∀ A t o o' → ∣ π A t ∣ + o ≡ o' → Γ ⊢tm t ∶ A → NS A →
             Seg Γ σ o (o₀Ty A) (π A t) → liftTy A o o' [ σ ]ty ≡ A
liftTy-sub {Γ} {σ} gr (arr ⋆ a b) t o o' e dt _ sg with tm-ty dt
... | arr-wf da db with ⋆-var da refl | ⋆-var db refl
...   | x , refl | y , refl =
  cong₂ (arr ⋆) (seg-head (path t) sg)
    (trans (cong (λ n → lookupₛ σ (vtx n)) (sym e))
      (trans (seg-end (path t) sg) (cong var (walk-end (walk t dt refl)))))
liftTy-sub {Γ} {σ} gr (arr (arr ⋆ s₀ t₀) a b) t o o' e dt _ sg =
  cong₃ arr (liftTy-sub gr (arr ⋆ s₀ t₀) a o o' e da tt sg)
            (liftN-sub gr a o da tt sg)
            (liftN-sub gr b o db tt (subst (Seg Γ σ o (o₀Ty (arr ⋆ s₀ t₀))) (PI gr t dt refl) sg))
  where
  da = arr-l′ (tm-ty dt)
  db = arr-r′ (tm-ty dt)
liftTy-sub gr (arr (arr (arr B s₁ t₁) s₀ t₀) a b) t o o' e dt _ sg =
  cong₃ arr (liftTy-sub gr (arr (arr B s₁ t₁) s₀ t₀) a o o' e da tt sg)
            (liftN-sub gr a o da tt sg)
            (liftN-sub gr b o db tt sg)
  where
  da = arr-l′ (tm-ty dt)
  db = arr-r′ (tm-ty dt)

------------------------------------------------------------------------
-- Full support: the lifted cell and its type use every variable of Θ_k.

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

  sc-fvTy : ∀ n A {m} → S.ScTy n A → m ∈ fvTy A → m < n
  sc-fvTy n ⋆ _ ()
  sc-fvTy n (arr A t u) (hA , ht , hu) mem with ∈-++ (fvTy A) (fvTm t ++ fvTm u) mem
  ... | inj₁ q = sc-fvTy n A hA q
  ... | inj₂ q with ∈-++ (fvTm t) (fvTm u) q
  ...   | inj₁ r = sc-fv n t ht r
  ...   | inj₂ r = sc-fv n u hu r

-- Every level of the segment of the 1-dimensional source occurs.
coverN : ∀ {Γ} A t o o' → ∣ π A t ∣ + o ≡ o' → Γ ⊢tm t ∶ A → NS A → ∀ m → InSeg o ∣ π A t ∣ m →
         m ∈ fvTmTy (liftN t o) (liftTy A o o')
coverN (arr ⋆ a b) t o o' e dt _ m h rewrite liftN-eq t o dt refl with lift-fs t o dt refl m h
... | inj₁ q        = ∈-++l (fvTm (lift t o)) _ q
... | inj₂ (inj₁ q) = ∈-++r (fvTm (lift t o)) _
                        (subst (_∈ vtx o ∷ vtx o' ∷ []) (sym q) (∈-here (vtx o) (vtx o' ∷ [])))
... | inj₂ (inj₂ q) = ∈-++r (fvTm (lift t o)) _
                        (∈-there {m} (vtx o) (vtx o' ∷ [])
                          (subst (_∈ vtx o' ∷ []) (sym (trans q (cong vtx e))) (∈-here (vtx o') [])))
coverN (arr (arr B s₀ t₀) a b) t o o' e dt _ m h
  with ∈-++ (fvTm (liftN a o)) (fvTy (liftTy (arr B s₀ t₀) o o'))
            (coverN (arr B s₀ t₀) a o o' e (arr-l′ (tm-ty dt)) tt m h)
... | inj₁ q = ∈-++r (fvTm (liftN t o)) _
                 (∈-++r (fvTy (liftTy (arr B s₀ t₀) o o')) _ (∈-++l (fvTm (liftN a o)) _ q))
... | inj₂ q = ∈-++r (fvTm (liftN t o)) _ (∈-++l (fvTy (liftTy (arr B s₀ t₀) o o')) _ q)

fs-cellN : ∀ {Γ K} A t → Γ ⊢tm t ∶ A → NS A → ∣ π A t ∣ ≡ K →
           chainC K ⊢tm liftN t 0 ∶ liftTy A 0 K →
           T (≈? (fvTmTy (liftN t 0) (liftTy A 0 K)) (varsCtx (chainC K)))
fs-cellN {K = K} A t dt ns e d̃ =
  ∧-intro (all-intro (λ x → elem x ys) xs (λ m mem → elem-downFrom (bound m mem)))
          (all-intro (λ x → elem x xs) ys
            (λ m mem → coverN A t 0 K (trans (+-zero _) e) dt ns m (inseg m (downFrom-mem (len (chainC K)) mem))))
  where
  ũ  = liftN t 0
  Ã  = liftTy A 0 K
  xs = fvTmTy ũ Ã
  ys = downFrom (len (chainC K))
  bound : ∀ m → m ∈ xs → m < len (chainC K)
  bound m mem with ∈-++ (fvTm ũ) (fvTy Ã) mem
  ... | inj₁ q = sc-fv (len (chainC K)) ũ (S.tm-sc closed d̃) q
  ... | inj₂ q = sc-fvTy (len (chainC K)) Ã (S.tm-ty-sc closed d̃) q
  inseg : ∀ m → m < len (chainC K) → InSeg 0 ∣ π A t ∣ m
  inseg m h = subst (λ n → InSeg 0 n m) (sym e) (inseg-all K m (subst (m <_) (len-chain K) h))

------------------------------------------------------------------------
-- The filler and the theorem.

-- The 1-dimensional source of a cell, with its type.
src1 : ∀ {Γ} A t → Γ ⊢tm t ∶ A → NS A →
       Σ Tm λ s → Σ Nat λ y → (Γ ⊢tm s ∶ arr ⋆ (var (o₀Ty A)) (var y)) × (π A t ≡ path s)
src1 (arr ⋆ a b) t dt _ with tm-ty dt
... | arr-wf da db with ⋆-var da refl | ⋆-var db refl
...   | x , refl | y , refl = t , y , dt , refl
src1 (arr (arr B s₀ t₀) a b) t dt _ = src1 (arr B s₀ t₀) a (arr-l′ (tm-ty dt)) tt

fillN : Ctx → Tm → Tm → Ty → Tm
fillN Γ u v A =
  coh (chainC ∣ π A u ∣) (arr (liftTy A 0 ∣ π A u ∣) (liftN u 0) (liftN v 0))
      (wsub Γ (o₀Ty A) (π A u))

totalN : ∀ {Γ u v B s t a b} → Graph Γ →
         Γ ⊢tm u ∶ arr (arr B s t) a b → Γ ⊢tm v ∶ arr (arr B s t) a b →
         Γ ⊢tm fillN Γ u v (arr (arr B s t) a b) ∶ arr (arr (arr B s t) a b) u v
totalN {Γ} {u} {v} {B} {s} {t} {a} {b} gr du dv =
  subst (Γ ⊢tm fillN Γ u v A ∶_) tyEq
    (coh-wf (ps (chainC-ps k)) (chainC-wf k) (arr-wf tu tv)
            (∨-inl (isOp (chainC k) Ã ũ ṽ)
                   (∧-intro (fs-cellN A u du tt refl tu) (fs-cellN A v dv tt refl tv)))
            sσ)
  where
  A  = arr (arr B s t) a b
  p  = π A u
  k  = ∣ p ∣
  Ã  = liftTy A 0 k
  ũ  = liftN u 0
  ṽ  = liftN v 0
  σ  = wsub Γ (o₀Ty A) p
  le : ∣ p ∣ + 0 ≤ k
  le = subst (_≤ k) (sym (+-zero k)) ≤-refl
  tu : chainC k ⊢tm ũ ∶ Ã
  tu = subst (λ n → chainC k ⊢tm ũ ∶ liftTy A 0 n) (+-zero k) (liftN-ty gr u 0 du tt le)
  tv : chainC k ⊢tm ṽ ∶ Ã
  tv = subst (λ n → chainC k ⊢tm ṽ ∶ liftTy A 0 n) (+-zero k) (liftN-ty gr v 0 dv tt le)
  sr = src1 A u du tt
  s₁ = fst sr
  y₁ = fst (snd sr)
  ds₁ : Γ ⊢tm s₁ ∶ arr ⋆ (var (o₀Ty A)) (var y₁)
  ds₁ = fst (snd (snd sr))
  wk : Walk Γ (o₀Ty A) p y₁
  wk = subst (λ q → Walk Γ (o₀Ty A) q y₁) (sym (snd (snd (snd sr)))) (walk s₁ ds₁ refl)
  sσ : Γ ⊢sub σ ∶ chainC k
  sσ = subst (λ n → Γ ⊢sub σ ∶ chainC n) (+-zero k)
             (wgo-ty (,-wf (⟨⟩-wf (tm-ctx du)) (fst (ends ds₁ refl))) refl wk)
  sg : Seg Γ σ 0 (o₀Ty A) p
  sg = wgo-seg p refl refl
  tyEq : arr Ã ũ ṽ [ σ ]ty ≡ arr A u v
  tyEq = cong₃ arr (liftTy-sub gr A u 0 k (+-zero k) du tt sg)
                   (liftN-sub gr u 0 du tt sg) (liftN-sub gr v 0 dv tt sg)
