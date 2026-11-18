------------------------------------------------------------------------
-- F2c, step (P5) of lemmas 3–5: the lift lemma.
--
-- Fix a globular Γ, a tree τ with Θ = ctxOf τ, and a relabelling f
-- that sends each variable y : A of Θ to a variable f y : A[λ] of Γ,
-- where λ = ρ f (len Θ) (LamTyped). For Γ ⊢ t : B and a diagram E of
-- Θ whose relabelling is the normal form of t,
--
--   lift : Lift5 t B E
--
-- i.e. liftT t E returns some t′ (at every fuel above the depth of t),
-- liftTy B E returns some B′, Θ ⊢ t′ : B′, t′[λ] ≡ t, B′[λ] ≡ B, and
-- the normal form of t′ is E.
--
-- By induction on the typing of t.
--   * A variable x: E has the shape of the globe of x, so it is the
--     globe of a variable y = top E of Θ (globe-root), with f y ≡ x;
--     the lift is var y, and its type lifts along the globe
--     (lift-glob-ty).
--   * A coherence coh Θ₁ A₁ σ₁: `assign` cuts E into positions P of
--     Θ₁'s variables (Assign, AssignTyped); the induction hypothesis
--     lifts each argument at its position, giving σ₁′; the lifted type
--     is A₁[σ₁′] by (P4) (LiftSub); `assign` at any fuel returns the
--     same positions (AssignUnique), so the lift is coh Θ₁ A₁ σ₁′.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Lift where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed; tm-unique)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (tm-ty)
open import CaTTExp.GlobularFiller
  using (LT; lt; bd; nf; wrap; top; flat; liftT; liftTy; liftS; assign; idTree; depthTm; depthSub; depthTy; module Lists)
open Lists using (find)
open import CaTTExp.GlobularTotal.Surj ∅ using (treeOf-ps)
open import CaTTExp.GlobularTotal.Uniq using (mem; memL; memCs; Ex; ExCs; Cell; dimOf)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn; ps-glob)
open import CaTTExp.GlobularTotal.LabEx using (lab-ex)
open import CaTTExp.GlobularTotal.LabRange using (lab-all)
open import CaTTExp.GlobularTotal.FlatBd using (flatG; Good; flat-is-flatG)
open import CaTTExp.GlobularTotal.NfSub using (Lab; flatG-cong; wrap-flat; lookup-∘)
open import CaTTExp.GlobularTotal.ExGood using (TypedImg; ex-good)
open import CaTTExp.GlobularTotal.NfTyped using (Glob; Ends; res-var)
open import CaTTExp.GlobularTotal.NfFuel using (nf-det; nf-≥; depth-look; sub-len; dim-sub)
open import CaTTExp.GlobularTotal.ImgTyped using (img-res; J; typed-img)
open import CaTTExp.GlobularTotal.CohParts using (flat-total; lab-of-mem; lt-lookup)
open import CaTTExp.GlobularTotal.NfCoh using (glob-shape; res; all-res)
open import CaTTExp.GlobularTotal.EndsNf using (ends-nf; ParB)
open import CaTTExp.GlobularTotal.Wrap using (wrapT; wrap-T; wrapT-ends)
open import CaTTExp.GlobularTotal.LabDistinct using (nd-idTree)
open import CaTTExp.GlobularTotal.Relabel using (relab; relabs; mapN)
open import CaTTExp.GlobularTotal.LamTyped using (ρ; look-ρ)
open import CaTTExp.GlobularTotal.Assign using (assign-ok; memKey)
open import CaTTExp.GlobularTotal.AssignTyped using (assign-typed)
open import CaTTExp.GlobularTotal.AssignUnique using (assign-flat)
open import CaTTExp.GlobularTotal.LiftSub using (lift-sub-ty; typos; liftS-ext; lab-at)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ x → (m ≡ just x) × (f x ≡ just b)
  bind-inv nothing  f ()
  bind-inv (just x) f e = x , refl , e

  bind-just : ∀ {A B : Set} (m : Maybe A) (k : A → Maybe B) {x} → m ≡ just x → (m >>= k) ≡ k x
  bind-just m k refl = refl

  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

  lt-split : ∀ a b → T (a <ℕ b) → Σ Nat λ i → b ≡ suc a + i
  lt-split a       zero    ()
  lt-split zero    (suc b) p = b , refl
  lt-split (suc a) (suc b) p with lt-split a b p
  ... | i , e = i , cong suc e

  ≤-+ : ∀ a i → T (a <ℕ suc (a + i))
  ≤-+ zero    i = tt
  ≤-+ (suc a) i = ≤-+ a i

  ≤-+r : ∀ a b → T (b <ℕ suc (a + b))
  ≤-+r zero    b = lt-suc b
    where
    lt-suc : ∀ a → T (a <ℕ suc a)
    lt-suc zero    = tt
    lt-suc (suc a) = lt-suc a
  ≤-+r (suc a) b = weak b (a + b) (≤-+r a b)
    where
    weak : ∀ a b → T (a <ℕ suc b) → T (a <ℕ suc (suc b))
    weak zero    b       p = tt
    weak (suc a) zero    ()
    weak (suc a) (suc b) p = weak a b p

  le-lt : ∀ a b c → T (a <ℕ suc b) → T (b <ℕ c) → T (a <ℕ c)
  le-lt zero    b       (suc c) p q = tt
  le-lt a       b       zero    p ()
  le-lt (suc a) zero    (suc c) () q
  le-lt (suc a) (suc b) (suc c) p q = le-lt a b c p q

  lt-suc : ∀ a → T (a <ℕ suc a)
  lt-suc zero    = tt
  lt-suc (suc a) = lt-suc a

  lt-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  lt-weak zero    b       p = tt
  lt-weak (suc a) zero    ()
  lt-weak (suc a) (suc b) p = lt-weak a b p

  lt-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  lt-ne zero    zero    ()
  lt-ne zero    (suc b) p = refl
  lt-ne (suc a) zero    ()
  lt-ne (suc a) (suc b) p = lt-ne a b p

  lt-ne' : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne' zero    zero    p ()
  lt-ne' zero    (suc n) p e = tt
  lt-ne' (suc y) zero    () e
  lt-ne' (suc y) (suc n) p e = lt-ne' y n p e

  ==-self : ∀ y → (y ==ℕ y) ≡ true
  ==-self y = T-≡ (==ℕ-refl y)

  lenₛ-∘ : ∀ τ σ → lenₛ (τ ∘ σ) ≡ lenₛ τ
  lenₛ-∘ ⟨⟩       σ = refl
  lenₛ-∘ (τ ,ₛ t) σ = cong suc (lenₛ-∘ τ σ)

  look-lt : ∀ σ y → T (depthTm (lookupₛ σ y) <ℕ suc (depthSub σ) + 0)
  look-lt σ y = subst (λ k → T (depthTm (lookupₛ σ y) <ℕ k)) (sym (+0 (suc (depthSub σ)))) (depth-look σ y)

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==ℕ-sound y (len Γ) (≡-T eq) = lt-suc (len Γ)
  ... | false = lt-weak y (len Γ) (lookup-lt Γ y A e)

  lookup-top : ∀ Γ C → lookup (Γ ▸ C) (len Γ) ≡ just C
  lookup-top Γ C rewrite ==-self (len Γ) = refl

  lookup-weak : ∀ Γ C y A → lookup Γ y ≡ just A → lookup (Γ ▸ C) y ≡ just A
  lookup-weak Γ C y A e rewrite lt-ne y (len Γ) (lookup-lt Γ y A e) = e

  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

  dim0 : ∀ A → dim A ≡ 0 → A ≡ ⋆
  dim0 ⋆           _ = refl
  dim0 (arr _ _ _) ()

  arr-inj₁ : ∀ {A A' t t' u u'} → arr A t u ≡ arr A' t' u' → A ≡ A'
  arr-inj₁ refl = refl

  find-memKey : ∀ y (as : List (Nat × LT)) X → find y as ≡ just X → memKey y as ≡ true
  find-memKey y []             X ()
  find-memKey y ((k , v) ∷ as) X e with y ==ℕ k
  ... | true  = refl
  ... | false = find-memKey y as X e

------------------------------------------------------------------------
-- Globes.

Glb : LT → Set
Glb (lt (y ∷ [])     [])       = ⊤
Glb (lt (a ∷ b ∷ []) (c ∷ [])) = Glb c
Glb _                          = ⊥

glb-relab : ∀ f E → Glb (relab f E) → Glb E
glb-relab f (lt []               cs)             ()
glb-relab f (lt (y ∷ [])         [])             g = tt
glb-relab f (lt (y ∷ [])         (c ∷ cs))       ()
glb-relab f (lt (a ∷ b ∷ [])     [])             ()
glb-relab f (lt (a ∷ b ∷ [])     (c ∷ []))       g = glb-relab f c g
glb-relab f (lt (a ∷ b ∷ [])     (c ∷ c' ∷ cs))  ()
glb-relab f (lt (a ∷ b ∷ x ∷ os) cs)             ()

glb-wrapT : ∀ B s → Glb s → Glb (wrapT B s)
glb-wrapT ⋆                           s g = g
glb-wrapT (arr B (var a) (var b))     s g = glb-wrapT B (lt (a ∷ b ∷ []) (s ∷ [])) g
glb-wrapT (arr B (var a) (coh _ _ _)) s g = g
glb-wrapT (arr B (var a) (cst _))     s g = g
glb-wrapT (arr B (coh _ _ _) _)       s g = g
glb-wrapT (arr B (cst _) _)           s g = g

top-wrapT : ∀ B s → top (wrapT B s) ≡ top s
top-wrapT ⋆                           s = refl
top-wrapT (arr B (var a) (var b))     s = top-wrapT B (lt (a ∷ b ∷ []) (s ∷ []))
top-wrapT (arr B (var a) (coh _ _ _)) s = refl
top-wrapT (arr B (var a) (cst _))     s = refl
top-wrapT (arr B (coh _ _ _) _)       s = refl
top-wrapT (arr B (cst _) _)           s = refl

top-relab : ∀ f E → Glb E → top (relab f E) ≡ f (top E)
top-relab f (lt (y ∷ [])     [])       g = refl
top-relab f (lt (a ∷ b ∷ []) (c ∷ [])) g = top-relab f c g

module _ (Θ : Ctx) (gΘ : Glob Θ) where

  -- A globe below the cell p → q: the globe of its top cell reaches it.
  globe-br : ∀ e p q E → Ex Θ e (just (p , q)) E → Glb E →
             Σ Ty λ C → (lookup Θ (top E) ≡ just C) × Σ Ty λ Cp → (lookup Θ p ≡ just Cp)
             × (wrapT C (lt (top E ∷ []) []) ≡ wrapT Cp (lt (p ∷ q ∷ []) (E ∷ [])))
  globe-br e p q (lt (y ∷ []) []) ((((B , ey) , _) , tt) , tt) g with gΘ y _ ey
  ... | _ , _ , ep , _ , _ = arr B (var p) (var q) , ey , B , ep , refl
  globe-br e p q (lt (a ∷ b ∷ []) (c ∷ [])) ((((Ba , ea) , _) , _ , tt) , (xc , tt)) g
    with globe-br (suc e) a b c xc g
  ... | C , eC , Ca , ea' , w with trans (sym ea) ea' | gΘ a _ ea
  ...   | refl | _ , _ , ep , _ , _ = C , eC , Ba , ep , w
  globe-br e p q (lt [] _) _ ()
  globe-br e p q (lt (y ∷ []) (_ ∷ _)) _ ()
  globe-br e p q (lt (a ∷ b ∷ []) []) _ ()
  globe-br e p q (lt (a ∷ b ∷ []) (_ ∷ _ ∷ _)) _ ()
  globe-br e p q (lt (a ∷ b ∷ _ ∷ _) _) _ ()

  -- A globe of Θ is the globe of its top variable.
  globe-root : ∀ E → Ex Θ 0 nothing E → Glb E →
               Σ Ty λ C → (lookup Θ (top E) ≡ just C) × (wrapT C (lt (top E ∷ []) []) ≡ E)
  globe-root (lt (y ∷ []) []) ((((A , eA) , dA) , tt) , tt) g
    with dim0 A (trans (sym (dimOf-just Θ y A eA)) dA)
  ... | refl = ⋆ , eA , refl
  globe-root (lt (a ∷ b ∷ []) (c ∷ [])) ((((Aa , ea) , da) , _ , tt) , (xc , tt)) g
    with globe-br 1 a b c xc g
  ... | C , eC , Ca , ea' , w with trans (sym ea) ea' | dim0 Aa (trans (sym (dimOf-just Θ a Aa ea)) da)
  ...   | refl | refl = C , eC , w
  globe-root (lt [] _) _ ()
  globe-root (lt (y ∷ []) (_ ∷ _)) _ ()
  globe-root (lt (a ∷ b ∷ []) []) _ ()
  globe-root (lt (a ∷ b ∷ []) (_ ∷ _ ∷ _)) _ ()
  globe-root (lt (a ∷ b ∷ _ ∷ _) _) _ ()

------------------------------------------------------------------------
-- Substitutions.

sub-eq : ∀ a b → lenₛ a ≡ lenₛ b → (∀ y → T (y <ℕ lenₛ a) → lookupₛ a y ≡ lookupₛ b y) → a ≡ b
sub-eq ⟨⟩       ⟨⟩       _ _ = refl
sub-eq ⟨⟩       (b ,ₛ t) () _
sub-eq (a ,ₛ s) ⟨⟩       () _
sub-eq (a ,ₛ s) (b ,ₛ t) l h = cong₂ _,ₛ_ (sub-eq a b l' h') st
  where
  l' = suc-inj l
  st : s ≡ t
  st with h (lenₛ a) (lt-suc (lenₛ a))
  ... | e rewrite ==-self (lenₛ a) | l' | ==-self (lenₛ b) = e
  h' : ∀ y → T (y <ℕ lenₛ a) → lookupₛ a y ≡ lookupₛ b y
  h' y p with h y (lt-weak y (lenₛ a) p)
  ... | e rewrite lt-ne y (lenₛ a) p | sym l' | lt-ne y (lenₛ a) p = e

module _ (Θ : Ctx) (dΘ : Θ ⊢ctx) where

  -- A substitution is typed when each of its terms is.
  sub-of-look : ∀ {Δ} → Δ ⊢ctx → ∀ σ′ → lenₛ σ′ ≡ len Δ →
                (∀ y A → lookup Δ y ≡ just A → Θ ⊢tm lookupₛ σ′ y ∶ A [ σ′ ]ty) → Θ ⊢sub σ′ ∶ Δ
  sub-of-look ε-wf ⟨⟩ _ _ = ⟨⟩-wf dΘ
  sub-of-look ε-wf (σ′ ,ₛ s) () _
  sub-of-look (▸-wf dΔ dA) ⟨⟩ () _
  sub-of-look {Δ ▸ A} (▸-wf dΔ dA) (σ″ ,ₛ s) l h =
    ,-wf (sub-of-look dΔ σ″ l' h') ds
    where
    l' = suc-inj l
    sc : S.ScTy (lenₛ σ″) A
    sc = subst (λ n → S.ScTy n A) (sym l') (S.ty-sc closed dA)
    ds : Θ ⊢tm s ∶ A [ σ″ ]ty
    ds with h (len Δ) A (lookup-top Δ A)
    ... | d rewrite sym l' | ==-self (lenₛ σ″) = subst (Θ ⊢tm s ∶_) (S.ext-ty A σ″ s sc) d
    h' : ∀ y A′ → lookup Δ y ≡ just A′ → Θ ⊢tm lookupₛ σ″ y ∶ A′ [ σ″ ]ty
    h' y A′ e with h y A′ (lookup-weak Δ A y A′ e)
    ... | d rewrite sym l' | lt-ne y (lenₛ σ″) (subst (λ n → T (y <ℕ n)) (sym l') (lookup-lt Δ y A′ e)) =
      subst (Θ ⊢tm lookupₛ σ″ y ∶_)
            (S.ext-ty A′ σ″ s (subst (λ n → S.ScTy n A′) (sym l') (snd (S.ctx-lookup closed dΔ e)))) d

-- liftS succeeds when each component lifts.
liftS-total : ∀ k Γ τ as i →
              (∀ z → T (z <ℕ i) → Σ Tm λ t → Σ LT λ X → (find z as ≡ just X) × (liftT k Γ (lookupₛ τ z) X ≡ just t)) →
              Σ Sub λ ρ′ → (liftS k Γ τ as i ≡ just ρ′) × (lenₛ ρ′ ≡ i)
                × (∀ z → T (z <ℕ i) → ∀ X → find z as ≡ just X → liftT k Γ (lookupₛ τ z) X ≡ just (lookupₛ ρ′ z))
liftS-total k Γ τ as zero    h = ⟨⟩ , refl , refl , λ z ()
liftS-total k Γ τ as (suc i) h with liftS-total k Γ τ as i (λ z p → h z (lt-weak z i p)) | h i (lt-suc i)
... | ρ′ , eρ , lρ , hρ | t , X , fX , lX = (ρ′ ,ₛ t) , eq , cong suc lρ , look
  where
  eq : liftS k Γ τ as (suc i) ≡ just (ρ′ ,ₛ t)
  eq rewrite eρ | fX | lX = refl
  look : ∀ z → T (z <ℕ suc i) → ∀ X′ → find z as ≡ just X′ → liftT k Γ (lookupₛ τ z) X′ ≡ just (lookupₛ (ρ′ ,ₛ t) z)
  look z p X′ e rewrite lρ with z ==ℕ i in ez
  ... | true rewrite ==ℕ-sound z i (≡-T ez) | just-inj (trans (sym e) fX) = lX
  ... | false = hρ z (lt-ne' z i p ez) X′ e

------------------------------------------------------------------------
-- The lemma.

module _ (Γ : Ctx) (gΓ : Glob Γ) (τ : Tree) (dΘ : ctxOf τ ⊢ctx) (f : Nat → Nat)
         (lf : ∀ y A → lookup (ctxOf τ) y ≡ just A → lookup Γ (f y) ≡ just (A [ ρ f (len (ctxOf τ)) ]ty)) where

  private
    Θ = ctxOf τ
    λσ = ρ f (len Θ)
    gΘ : Glob Θ
    gΘ = ps-glob (snd (psOf τ))

  Lift5 : Tm → Ty → LT → Set
  Lift5 t B E = Σ Tm λ t′ → Σ Ty λ B′ →
      (∀ k → T (depthTm t <ℕ k) → liftT k Γ t E ≡ just t′)
    × (∀ k → T (depthTy B <ℕ k) → liftTy k Γ B E ≡ just B′)
    × (Θ ⊢tm t′ ∶ B′) × (t′ [ λσ ]tm ≡ t) × (B′ [ λσ ]ty ≡ B)
    × (Σ Nat λ n → nf n Θ t′ ≡ just E)

  private
    arr-step : ∀ k B a b E B′ a′ b′ → liftTy k Γ B (bd false (dim B) E) ≡ just B′ →
               liftT k Γ a (bd false (dim B) E) ≡ just a′ → liftT k Γ b (bd true (dim B) E) ≡ just b′ →
               liftTy k Γ (arr B a b) E ≡ just (arr B′ a′ b′)
    arr-step k B a b E B′ a′ b′ e₁ e₂ e₃ rewrite e₁ | e₂ | e₃ = refl

  -- The type of a variable lifts along its globe.
  lift-glob-ty : ∀ B → TyIn Γ B → ∀ y C → lookup Θ y ≡ just C → C [ λσ ]ty ≡ B →
                 ∀ k → liftTy (suc k) Γ B (wrapT C (lt (y ∷ []) [])) ≡ just C
  lift-glob-ty ⋆ _ y ⋆           eC eλ k = refl
  lift-glob-ty ⋆ _ y (arr _ _ _) eC ()  k
  lift-glob-ty (arr B₀ (var a) (var b)) (_ , _ , _ , _ , tB₀) y C eC eλ k with gΘ y C eC
  lift-glob-ty (arr B₀ (var a) (var b)) (_ , _ , _ , _ , tB₀) y ⋆ eC () k | _
  lift-glob-ty (arr B₀ (var a) (var b)) (_ , _ , _ , _ , tB₀) y (arr C₀ (var p) (var q)) eC eλ k
    | _ , _ , ep , _ , tC₀ =
    arr-step (suc k) B₀ (var a) (var b) W C₀ (var p) (var q) e₁
      (cong (λ X → just (var (top X))) bd₀ ∙′ cong (λ z → just (var z)) (top-wrapT C₀ (lt (p ∷ []) [])))
      (cong (λ X → just (var (top X))) bd₁ ∙′ cong (λ z → just (var z)) (top-wrapT C₀ (lt (q ∷ []) [])))
    where
    _∙′_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    _∙′_ = trans
    W = wrapT (arr C₀ (var p) (var q)) (lt (y ∷ []) [])
    e0 : C₀ [ λσ ]ty ≡ B₀
    e0 = arr-inj₁ eλ
    dd : dim B₀ ≡ dim C₀
    dd = trans (cong dim (sym e0)) (dim-sub C₀ λσ)
    bd₀ : bd false (dim B₀) W ≡ wrapT C₀ (lt (p ∷ []) [])
    bd₀ = trans (cong (λ j → bd false j W) dd) (fst (wrapT-ends Θ C₀ p q (lt (y ∷ []) []) tC₀))
    bd₁ : bd true (dim B₀) W ≡ wrapT C₀ (lt (q ∷ []) [])
    bd₁ = trans (cong (λ j → bd true j W) dd) (snd (wrapT-ends Θ C₀ p q (lt (y ∷ []) []) tC₀))
    e₁ : liftTy (suc k) Γ B₀ (bd false (dim B₀) W) ≡ just C₀
    e₁ = trans (cong (liftTy (suc k) Γ B₀) bd₀) (lift-glob-ty B₀ tB₀ p C₀ ep e0 k)
  lift-glob-ty (arr B₀ (var a) (var b)) _ y (arr C₀ (var p) (coh _ _ _)) eC eλ k | ()
  lift-glob-ty (arr B₀ (var a) (var b)) _ y (arr C₀ (var p) (cst _)) eC eλ k | ()
  lift-glob-ty (arr B₀ (var a) (var b)) _ y (arr C₀ (coh _ _ _) _) eC eλ k | ()
  lift-glob-ty (arr B₀ (var a) (var b)) _ y (arr C₀ (cst _) _) eC eλ k | ()
  lift-glob-ty (arr B₀ (var a) (coh _ _ _)) () y C eC eλ k
  lift-glob-ty (arr B₀ (var a) (cst _))     () y C eC eλ k
  lift-glob-ty (arr B₀ (coh _ _ _) _)       () y C eC eλ k
  lift-glob-ty (arr B₀ (cst _) _)           () y C eC eλ k

  -- The variable case.
  lift-var : ∀ x B → lookup Γ x ≡ just B → ∀ E → Ex Θ 0 nothing E →
             (Σ Nat λ m → nf m Γ (var x) ≡ just (relab f E)) → Lift5 (var x) B E
  lift-var x B ex E xE (zero , ())
  lift-var x B ex E xE (suc m , eN) =
    var y , C , lT , lTy , var-wf dΘ eC , vλ , Cλ , (1 , nfy)
    where
    tB = gΓ x B ex
    rE : relab f E ≡ wrapT B (lt (x ∷ []) [])
    rE = just-inj (trans (sym eN) (trans (bind-just (lookup Γ x) _ ex) (wrap-T Γ B _ tB)))
    gE : Glb E
    gE = glb-relab f E (subst Glb (sym rE) (glb-wrapT B (lt (x ∷ []) []) tt))
    G = globe-root Θ gΘ E xE gE
    y = top E
    C = fst G
    eC : lookup Θ y ≡ just C
    eC = fst (snd G)
    wE : wrapT C (lt (y ∷ []) []) ≡ E
    wE = snd (snd G)
    fy : f y ≡ x
    fy = trans (sym (top-relab f E gE)) (trans (cong top rE) (top-wrapT B (lt (x ∷ []) [])))
    Cλ : C [ λσ ]ty ≡ B
    Cλ = just-inj (trans (sym (lf y C eC)) (subst (λ z → lookup Γ z ≡ just B) (sym fy) ex))
    lT : ∀ k → T (0 <ℕ k) → liftT k Γ (var x) E ≡ just (var y)
    lT zero    ()
    lT (suc k) _ = refl
    lTy : ∀ k → T (depthTy B <ℕ k) → liftTy k Γ B E ≡ just C
    lTy zero    ()
    lTy (suc k) _ = subst (λ W → liftTy (suc k) Γ B W ≡ just C) wE (lift-glob-ty B tB y C eC Cλ k)
    vλ : lookupₛ λσ y ≡ var x
    vλ = trans (look-ρ f (len Θ) y (lookup-lt Θ y C eC)) (cong var fy)
    nfy : nf 1 Θ (var y) ≡ just E
    nfy = trans (bind-just (lookup Θ y) _ eC) (trans (wrap-T Θ C _ (gΘ y C eC)) (cong just wE))

  private
    parB : ∀ {Θ′} B au av → Ends Θ′ B au → Ends Θ′ B av → ParB B au av
    parB ⋆ _ _ _ _ = tt
    parB {Θ′} (arr B' s t) au av (n , es , _) (n' , es' , _) = nf-det n n' Θ′ s _ _ es es'

    Comp : Tm → LT → Set
    Comp t X = Σ Ty λ By → (Γ ⊢tm t ∶ By) × Lift5 t By X

    lT-of : ∀ {t X} (c : Comp t X) → ∀ k → T (depthTm t <ℕ k) → liftT k Γ t X ≡ just (fst (snd (snd c)))
    lT-of (_ , _ , _ , _ , l , _) = l

  -- The coherence case, given the lemma for the arguments.
  module _ (tr₁ : Tree) (B₁ : Ty) (u₁ v₁ : Tm) (σ₁ : Sub)
           (etr₁ : treeOf (ctxOf tr₁) ≡ just tr₁) (pΘ₁ : ctxOf tr₁ ⊢ps) (dΘ₁ : ctxOf tr₁ ⊢ctx)
           (du : ctxOf tr₁ ⊢tm u₁ ∶ B₁) (dv : ctxOf tr₁ ⊢tm v₁ ∶ B₁)
           (sd : T (cattSide (ctxOf tr₁) B₁ u₁ v₁)) (dσ₁ : Γ ⊢sub σ₁ ∶ ctxOf tr₁)
           (ih : ∀ y → T (y <ℕ lenₛ σ₁) → ∀ X → Ex Θ 0 nothing X →
                 (Σ Nat λ m → nf m Γ (lookupₛ σ₁ y) ≡ just (relab f X)) → Comp (lookupₛ σ₁ y) X)
           (E : LT) (xE : Ex Θ 0 nothing E) (m : Nat)
           (eN : nf m Γ (coh (ctxOf tr₁) (arr B₁ u₁ v₁) σ₁) ≡ just (relab f E)) where

    private
      Θ₁ = ctxOf tr₁
      I₁ = idTree tr₁
      A₁ = arr B₁ u₁ v₁
      d = depthSub σ₁
      gΘ₁ = ps-glob pΘ₁
      ar = all-res gΓ dσ₁
      ir = img-res Γ dσ₁ ar dΘ₁ (glob-shape Θ₁ gΘ₁)
      J₀ = J Γ σ₁ Θ₁ 0
      ti₀ : TypedImg Θ₁ J₀
      ti₀ = typed-img Γ σ₁ Θ₁ 0 gΘ₁ ir
      good₀ = ex-good Θ₁ J₀ ti₀ 0 I₁ (lab-ex tr₁)
      c₀ = fst (flat-total J₀ 0 (λ _ → ⊤) I₁ good₀)
      e₀ : flatG J₀ 0 I₁ ≡ just c₀
      e₀ = snd (flat-total J₀ 0 (λ _ → ⊤) I₁ good₀)
      nf₀ : nf (suc (suc d + 0)) Γ (coh Θ₁ A₁ σ₁) ≡ just c₀
      nf₀ = trans (bind-just (treeOf Θ₁) _ etr₁) (trans (flat-is-flatG (suc d + 0) Γ σ₁ 0 I₁) e₀)
      rE : relab f E ≡ c₀
      rE = nf-det m (suc (suc d + 0)) Γ (coh Θ₁ A₁ σ₁) (relab f E) c₀ eN nf₀

      -- positions
      AS = assign-ok Γ σ₁ (suc d + 0) Θ f 0 (λ _ → ⊤) I₁ E c₀ good₀ e₀ rE xE (nd-idTree tr₁)
      as₀ = fst AS
      inv = snd (snd AS)
      i1 = fst inv
      i2 : flatG (λ y → find y as₀) 0 I₁ ≡ just E
      i2 = fst (snd inv)
      i4 = snd (snd (snd inv))
      P : Nat → Maybe LT
      P y = find y as₀
      tiP : TypedImg Θ₁ P
      tiP = assign-typed Γ σ₁ (suc d + 0) Θ f tr₁ E as₀ inv gΘ₁ ti₀

      memI : ∀ y → T (y <ℕ lenₛ σ₁) → mem y I₁ ≡ true
      memI y q = trans (lab-all tr₁ y) (T-≡ (subst (λ l → T (y <ℕ l)) (sub-len dσ₁) q))

      inσ : ∀ y → mem y I₁ ≡ true → T (y <ℕ lenₛ σ₁)
      inσ y mm = subst (λ l → T (y <ℕ l)) (sym (sub-len dσ₁)) (≡-T (trans (sym (lab-all tr₁ y)) mm))

      P-in : ∀ y X → P y ≡ just X → T (y <ℕ lenₛ σ₁)
      P-in y X e = inσ y (trans (sym (i4 y)) (find-memKey y as₀ X e))

      -- the position of each argument and its lift
      pos : ∀ y → T (y <ℕ lenₛ σ₁) → Σ LT λ X → (P y ≡ just X) × Ex Θ 0 nothing X × (J₀ y ≡ just (relab f X))
      pos y q with i1 y (memI y q)
      ... | X , fX , xX , jX , _ = X , fX , xX , jX

      comp : ∀ y → (q : T (y <ℕ lenₛ σ₁)) → Comp (lookupₛ σ₁ y) (fst (pos y q))
      comp y q = ih y q (fst (pos y q)) (fst (snd (snd (pos y q)))) (suc d + 0 , snd (snd (snd (pos y q))))

      t′ : ∀ y → T (y <ℕ lenₛ σ₁) → Tm
      t′ y q = fst (snd (snd (comp y q)))

      -- the lifted arguments
      L = liftS-total (suc d + 0) Γ σ₁ as₀ (len Θ₁)
            (λ z p → t′ z (q z p) , fst (pos z (q z p)) , fst (snd (pos z (q z p))) ,
                     lT-of (comp z (q z p)) (suc d + 0) (look-lt σ₁ z))
        where
        q : ∀ z → T (z <ℕ len Θ₁) → T (z <ℕ lenₛ σ₁)
        q z p = subst (λ l → T (z <ℕ l)) (sym (sub-len dσ₁)) p
      σ′ = fst L
      lσ′ : lenₛ σ′ ≡ len Θ₁
      lσ′ = fst (snd (snd L))

      look′ : ∀ y (q : T (y <ℕ lenₛ σ₁)) → lookupₛ σ′ y ≡ t′ y q
      look′ y q = just-inj (trans (sym h₁) h₂)
        where
        h₁ = snd (snd (snd L)) y (subst (λ l → T (y <ℕ l)) (sub-len dσ₁) q) (fst (pos y q)) (fst (snd (pos y q)))
        h₂ = lT-of (comp y q) (suc d + 0) (look-lt σ₁ y)

      -- hypotheses of (P4)
      rel : ∀ y X → P y ≡ just X → ∀ k → T (depthTm (lookupₛ σ₁ y) <ℕ k) →
            nf k Γ (lookupₛ σ₁ y) ≡ just (relab f X)
      rel y X e k p with P-in y X e
      ... | q with pos y q | lt-lookup Θ₁ y (subst (λ l → T (y <ℕ l)) (sub-len dσ₁) q)
      ...   | X′ , fX′ , _ , jX′ | A , eA with ir y A eA | lt-split (depthTm (lookupₛ σ₁ y)) k p
      ...     | x , fx , _ | i , refl with just-inj (trans (sym e) fX′)
      ...       | refl = trans (fx i) (cong just (nf-det (suc (depthTm (lookupₛ σ₁ y)) + 0) (suc d + 0) Γ (lookupₛ σ₁ y) x (relab f X) (fx 0) jX′))

      lifts : ∀ y X → P y ≡ just X → ∀ k → T (depthTm (lookupₛ σ₁ y) <ℕ k) →
              liftT k Γ (lookupₛ σ₁ y) X ≡ just (lookupₛ σ′ y)
      lifts y X e k p with P-in y X e
      ... | q with just-inj (trans (sym e) (fst (snd (pos y q))))
      ...   | refl = trans (lT-of (comp y q) k p) (cong just (sym (look′ y q)))

      -- each lifted argument has the lifted type
      arg-typed : ∀ y A → lookup Θ₁ y ≡ just A → Θ ⊢tm lookupₛ σ′ y ∶ A [ σ′ ]ty
      arg-typed y A eA = subst (λ t → Θ ⊢tm t ∶ A [ σ′ ]ty) (sym (look′ y q)) (subst (Θ ⊢tm t′ y q ∶_) B′≡ dt′)
        where
        q = subst (λ l → T (y <ℕ l)) (sym (sub-len dσ₁)) (lookup-lt Θ₁ y A eA)
        c = comp y q
        X = fst (pos y q)
        By≡ : fst c ≡ A [ σ₁ ]ty
        By≡ = tm-unique (fst (snd c)) (S.lookup-sub closed dΘ₁ eA dσ₁)
        L5 = snd (snd c)
        B′ = fst (snd L5)
        dt′ : Θ ⊢tm t′ y q ∶ B′
        dt′ = fst (snd (snd (snd (snd L5))))
        rv = res-var Θ₁ y A gΘ₁ eA
        n₀ = fst rv
        w = fst (snd rv)
        ew : nf 1 Θ₁ (var y) ≡ just w
        ew = fst (snd (snd rv))
        fw : flatG P 0 w ≡ just X
        fw = trans (wrap-flat P (fst b) (lt (y ∷ []) []) w 0 (snd (snd b))) (fst (snd (pos y q)))
          where
          b = bind-inv (lookup Θ₁ y) _ ew
        tp = typos Γ gΓ f Θ₁ gΘ₁ dΘ₁ σ₁ σ′ dσ₁ P tiP rel lifts A (tm-ty (var-wf dΘ₁ eA)) w X
                   (fst (snd (snd (snd (snd (snd rv))))))
                   (fst (snd (snd (snd (snd (snd (snd rv)))))))
                   fw
        k = suc (depthTy (A [ σ₁ ]ty))
        B′≡ : B′ ≡ A [ σ′ ]ty
        B′≡ = just-inj (trans (sym (fst (snd (snd (snd L5))) k (subst (λ B → T (depthTy B <ℕ k)) (sym By≡) (lt-suc (depthTy (A [ σ₁ ]ty))))))
                              (subst (λ B → liftTy k Γ B X ≡ just (A [ σ′ ]ty)) (sym By≡)
                                 (lift-sub-ty Γ gΓ f Θ₁ gΘ₁ dΘ₁ σ₁ σ′ dσ₁ P tiP rel lifts A (tm-ty (var-wf dΘ₁ eA)) X k tp
                                    (lt-suc (depthTy (A [ σ₁ ]ty))))))

      dσ′ : Θ ⊢sub σ′ ∶ Θ₁
      dσ′ = sub-of-look Θ dΘ dΘ₁ σ′ lσ′ arg-typed

      -- the endpoints of the coherence's type, at Θ₁'s boundaries
      ru = res gΘ₁ du
      rv = res gΘ₁ dv
      au = fst ru
      av = fst rv
      en = ends-nf tr₁ B₁ u₁ v₁ au av
             (fst (snd (snd (snd (snd ru))))) (fst (snd (snd (snd (snd rv)))))
             (fst (snd (snd (snd ru)))) (fst (snd (snd (snd rv))))
             (snd (snd (snd (snd (snd (snd ru)))))) (snd (snd (snd (snd (snd (snd rv))))))
             (parB B₁ au av (fst (snd (snd (snd (snd (snd ru)))))) (fst (snd (snd (snd (snd (snd rv)))))))
             sd
      N = suc (depthTm u₁ + depthTm v₁)
      nu : nf N Θ₁ u₁ ≡ just au
      nu = fst (snd ru) (depthTm v₁)
      nv : nf N Θ₁ v₁ ≡ just av
      nv = nf-≥ (suc (depthTm v₁) + 0) N Θ₁ v₁ av (fst (snd rv) 0)
             (subst (λ k → T (k <ℕ suc N)) (sym (+0 (suc (depthTm v₁)))) (≤-+r (depthTm u₁) (depthTm v₁)))
      ends₁ : Ends Θ₁ A₁ I₁
      ends₁ = N , trans nu (cong just (fst en)) , trans nv (cong just (fst (snd en)))

      tyL : ∀ k → T (depthTy (A₁ [ σ₁ ]ty) <ℕ k) → liftTy k Γ (A₁ [ σ₁ ]ty) E ≡ just (A₁ [ σ′ ]ty)
      tyL k p = lift-sub-ty Γ gΓ f Θ₁ gΘ₁ dΘ₁ σ₁ σ′ dσ₁ P tiP rel lifts A₁ (arr-wf du dv) E k
                  (typos Γ gΓ f Θ₁ gΘ₁ dΘ₁ σ₁ σ′ dσ₁ P tiP rel lifts A₁ (arr-wf du dv) I₁ E (lab-ex tr₁) ends₁ i2) p

      goodP = ex-good Θ₁ P tiP 0 I₁ (lab-ex tr₁)

      -- the lift, at every fuel
      lT : ∀ k → T (depthTm (coh Θ₁ A₁ σ₁) <ℕ k) → liftT k Γ (coh Θ₁ A₁ σ₁) E ≡ just (coh Θ₁ A₁ σ′)
      lT zero    ()
      lT (suc k) p =
        trans (bind-just (treeOf Θ₁) (λ τ′ → assign k Γ σ₁ 0 (idTree τ′) E >>= λ as →
                                         liftS k Γ σ₁ as (len Θ₁) >>= λ s → just (coh Θ₁ A₁ s)) etr₁)
          (trans (bind-just (assign k Γ σ₁ 0 I₁ E) (λ as → liftS k Γ σ₁ as (len Θ₁) >>= λ s → just (coh Θ₁ A₁ s)) e-as)
                 (bind-just (liftS k Γ σ₁ as′ (len Θ₁)) (λ s → just (coh Θ₁ A₁ s)) e-ls))
        where
        dk : ∀ z → T (depthTm (lookupₛ σ₁ z) <ℕ k)
        dk z = le-lt _ d k (depth-look σ₁ z) p
        AF = assign-flat Γ σ₁ k f P 0 (λ _ → ⊤) I₁ E goodP i2 (nd-idTree tr₁)
               (lab-of-mem _ I₁ (λ z _ X e → rel z X e k (dk z)))
        as′ = fst AF
        e-as : assign k Γ σ₁ 0 I₁ E ≡ just as′
        e-as = fst (snd AF)
        fas = snd (snd (snd AF))
        comp′ : ∀ z → T (z <ℕ lenₛ σ′) → Σ LT λ X → (find z as′ ≡ just X)
                × (liftT k Γ (lookupₛ σ₁ z) X ≡ just (lookupₛ σ′ z))
        comp′ z pz = fst (pos z q) , trans (lab-at z I₁ fas (memI z q)) (fst (snd (pos z q))) ,
                     lifts z (fst (pos z q)) (fst (snd (pos z q))) k (dk z)
          where
          q = subst (λ l → T (z <ℕ l)) (trans lσ′ (sym (sub-len dσ₁))) pz
        e-ls : liftS k Γ σ₁ as′ (len Θ₁) ≡ just σ′
        e-ls = subst (λ l → liftS k Γ σ₁ as′ l ≡ just σ′) lσ′ (liftS-ext k Γ σ₁ as′ σ′ comp′)

      -- substituting back
      σλ : (σ′ ∘ λσ) ≡ σ₁
      σλ = sub-eq (σ′ ∘ λσ) σ₁ (trans (lenₛ-∘ σ′ λσ) (trans lσ′ (sym (sub-len dσ₁)))) h
        where
        h : ∀ y → T (y <ℕ lenₛ (σ′ ∘ λσ)) → lookupₛ (σ′ ∘ λσ) y ≡ lookupₛ σ₁ y
        h y p = trans (lookup-∘ σ′ λσ y p′) (trans (cong (_[ λσ ]tm) (look′ y q)) (λt (comp y q)))
          where
          p′ = subst (λ l → T (y <ℕ l)) (lenₛ-∘ σ′ λσ) p
          q = subst (λ l → T (y <ℕ l)) (trans lσ′ (sym (sub-len dσ₁))) p′
          λt : ∀ {t X} (c : Comp t X) → fst (snd (snd c)) [ λσ ]tm ≡ t
          λt (_ , _ , _ , _ , _ , _ , _ , e , _) = e

      tyλ : (A₁ [ σ′ ]ty) [ λσ ]ty ≡ A₁ [ σ₁ ]ty
      tyλ = trans (S.assoc-ty A₁ σ′ λσ (subst (λ n → S.ScTy n A₁) (sym lσ′) (S.ty-sc closed (arr-wf du dv))))
                  (cong (A₁ [_]ty) σλ)

      -- the normal form of the lift
      nfΘ : nf (suc (suc (depthSub σ′) + 0)) Θ (coh Θ₁ A₁ σ′) ≡ just E
      nfΘ = trans (bind-just (treeOf Θ₁) (λ τ′ → flat (suc (depthSub σ′) + 0) Θ σ′ 0 (idTree τ′)) etr₁)
              (trans (flat-is-flatG (suc (depthSub σ′) + 0) Θ σ′ 0 I₁)
                (trans (flatG-cong (λ y → nf (suc (depthSub σ′) + 0) Θ (lookupₛ σ′ y)) P 0 I₁ (lab-of-mem _ I₁ h)) i2))
        where
        nfc : ∀ {t X} (c : Comp t X) → Σ Nat λ n → nf n Θ (fst (snd (snd c))) ≡ just X
        nfc (_ , _ , _ , _ , _ , _ , _ , _ , _ , e) = e

        h : ∀ z → mem z I₁ ≡ true → nf (suc (depthSub σ′) + 0) Θ (lookupₛ σ′ z) ≡ P z
        h z mm = trans (cong (λ n → nf n Θ (lookupₛ σ′ z)) e)
                   (trans (fr i) (trans (cong just rX) (sym (fst (snd (pos z q))))))
          where
          q = inσ z mm
          LA = lt-lookup Θ₁ z (subst (λ l → T (z <ℕ l)) (sub-len dσ₁) q)
          R = res gΘ (arg-typed z (fst LA) (snd LA))
          r = fst R
          fr : ∀ m → nf (suc (depthTm (lookupₛ σ′ z)) + m) Θ (lookupₛ σ′ z) ≡ just r
          fr = fst (snd R)
          S = lt-split (depthTm (lookupₛ σ′ z)) (suc (depthSub σ′) + 0) (look-lt σ′ z)
          i = fst S
          e : suc (depthSub σ′) + 0 ≡ suc (depthTm (lookupₛ σ′ z)) + i
          e = snd S
          c = comp z q
          rX : r ≡ fst (pos z q)
          rX = nf-det (suc (depthTm (lookupₛ σ′ z)) + 0) (fst (nfc c)) Θ (lookupₛ σ′ z) r (fst (pos z q)) (fr 0)
                 (subst (λ t → nf (fst (nfc c)) Θ t ≡ just (fst (pos z q))) (sym (look′ z q)) (snd (nfc c)))

    lift-coh : Lift5 (coh Θ₁ A₁ σ₁) (A₁ [ σ₁ ]ty) E
    lift-coh = coh Θ₁ A₁ σ′ , A₁ [ σ′ ]ty , lT , tyL ,
               coh-wf pΘ₁ dΘ₁ (arr-wf du dv) sd dσ′ , cong (coh Θ₁ A₁) σλ , tyλ ,
               (suc (suc (depthSub σ′) + 0) , nfΘ)

  mutual
    lift : ∀ {t B} → Γ ⊢tm t ∶ B → ∀ E → Ex Θ 0 nothing E →
           (Σ Nat λ m → nf m Γ t ≡ just (relab f E)) → Lift5 t B E
    lift (var-wf {i} {A} _ e) E xE h = lift-var i A e E xE h
    lift (coh-wf {Θ₁} {B₁} {u₁} {v₁} {σ₁} pΘ₁ dΘ₁ (arr-wf du dv) sd dσ₁) E xE (m , eN)
      with treeOf-ps pΘ₁
    ... | tr₁ , etr₁ , refl =
      lift-coh tr₁ B₁ u₁ v₁ σ₁ etr₁ pΘ₁ dΘ₁ du dv sd dσ₁ (liftS′ dσ₁) E xE m eN
    lift (cst-wf {k = ()} _ _) E xE h

    liftS′ : ∀ {σ Δ} → Γ ⊢sub σ ∶ Δ → ∀ y → T (y <ℕ lenₛ σ) → ∀ X → Ex Θ 0 nothing X →
             (Σ Nat λ m → nf m Γ (lookupₛ σ y) ≡ just (relab f X)) → Comp (lookupₛ σ y) X
    liftS′ (⟨⟩-wf _) y ()
    liftS′ (,-wf {τ} dτ dt) y q with y ==ℕ lenₛ τ in eq
    ... | true  = λ X xX h → _ , dt , lift dt X xX h
    ... | false = liftS′ dτ y (lt-ne' y (lenₛ τ) q eq)
