------------------------------------------------------------------------
-- Totality of the discreteness filler on 1-cells (open-issues F2a,
-- the 1-dimensional case).
--
-- For every pure CaTT context Γ and every two 1-cells
--
--   Γ ⊢ u ∶ a → b      Γ ⊢ v ∶ a → b      with  path u ≡ path v,
--
-- the term  fill₁ Γ u v (a → b)  is a well-typed 2-cell u → v
-- (Theorem `total` at the end). Here `path` lists the 1-dimensional
-- variables a 1-cell is built from, in order. Nothing is assumed about Γ
-- beyond the two typing derivations: Γ may have cells of any dimension,
-- and the theorem is about its 1-cells. A graph context is the case
-- where every variable has dimension ≤ 1.
--
-- The filler is the canonical lift of `ordinary-math.md` §3:
--
--   fill₁ Γ u v (a → b) = coh Θ_k (lift u 0 →_{x₀ → x_k} lift v 0) [σ]
--
-- where k = |path u|, Θ_k is the chain context, σ : Θ_k → Γ picks the
-- vertices and edges of the walk of u, and `lift` re-reads u inside Θ_k
-- by giving its i-th edge occurrence the i-th edge of Θ_k. Unlike
-- CaTTExp.GraphFiller, everything here is structural: no fuel, and the
-- result is proved well typed for all inputs instead of checked.
--
-- The proof: every 1-dimensional coh is over a chain from its first
-- to its last object (CaTTExp.GraphFillerTotal.Chains, chain-side);
-- the lift is well typed (lift-ty) and has full support (lift-fs); the
-- path of a 1-cell is a walk from its source to its target (walk);
-- substituting σ back into the lift gives the original term (lift-sub).
------------------------------------------------------------------------
module CaTTExp.GraphFillerTotal where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GraphFillerTotal.Chains
open import CaTTExp.Weakening ∅ cattSide using (wk-ty)
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S

------------------------------------------------------------------------
-- Paths and lifts.

∣_∣ : List Nat → Nat
∣ [] ∣     = 0
∣ _ ∷ p ∣ = suc ∣ p ∣

∣++∣ : ∀ p q → ∣ p ++ q ∣ ≡ ∣ p ∣ + ∣ q ∣
∣++∣ []      q = refl
∣++∣ (_ ∷ p) q = cong suc (∣++∣ p q)

mutual
  -- The 1-dimensional variables of a 1-cell, in order.
  path : Tm → List Nat
  path (var i)     = i ∷ []
  path (coh _ _ τ) = pathCh τ
  path (cst ())

  -- Over a chain, the paths of the arguments at the edges.
  pathCh : Sub → List Nat
  pathCh ⟨⟩              = []
  pathCh (⟨⟩ ,ₛ _)       = []
  pathCh (τ ,ₛ _ ,ₛ e)   = pathCh τ ++ path e

mutual
  -- `lift u o`: u re-read inside a chain, its path starting at x_o.
  lift : Tm → Nat → Tm
  lift (var _)     o = var (edge (suc o))
  lift (coh Θ A τ) o = coh Θ A (liftCh τ o)
  lift (cst ())    o

  liftCh : Sub → Nat → Sub
  liftCh ⟨⟩            o = ⟨⟩
  liftCh (⟨⟩ ,ₛ _)     o = ⟨⟩ ,ₛ var (vtx o)
  liftCh (τ ,ₛ _ ,ₛ e) o =
    liftCh τ o ,ₛ var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o))) ,ₛ lift e (∣ pathCh τ ∣ + o)

------------------------------------------------------------------------
-- Walks and the substitution σ.

-- The target of an edge variable (0 when e is not an edge).
tgtOf : Ctx → Nat → Nat
tgtOf Γ e with lookup Γ e
... | just (arr _ _ (var b)) = b
... | _                      = 0

endOf : Ctx → Nat → List Nat → Nat
endOf Γ x []      = x
endOf Γ x (e ∷ p) = endOf Γ (tgtOf Γ e) p

data Walk (Γ : Ctx) : Nat → List Nat → Nat → Set where
  nil  : ∀ {x} → Walk Γ x [] x
  cons : ∀ {x z y e p} → lookup Γ e ≡ just (arr ⋆ (var x) (var z)) →
         Walk Γ z p y → Walk Γ x (e ∷ p) y

-- σ for a walk from a along p: x₀ = a, then (x_{i+1}, e_{i+1}) pairs.
wgo : Ctx → Sub → Nat → List Nat → Sub
wgo Γ σ x []      = σ
wgo Γ σ x (e ∷ p) = wgo Γ (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p

wsub : Ctx → Nat → List Nat → Sub
wsub Γ a p = wgo Γ (⟨⟩ ,ₛ var a) a p

------------------------------------------------------------------------
-- The filler.

fill₁ : Ctx → Tm → Tm → Ty → Tm
fill₁ Γ u v (arr ⋆ (var a) _) =
  coh (chainC ∣ path u ∣)
      (arr (arr ⋆ (var 0) (var (vtx ∣ path u ∣))) (lift u 0) (lift v 0))
      (wsub Γ a (path u))
fill₁ Γ u v _ = u      -- not a type of 1-cells between objects: unused

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

-- Terms of type ⋆ are variables.
⋆-var : ∀ {Γ t B} → Γ ⊢tm t ∶ B → B ≡ ⋆ → Σ Nat λ j → t ≡ var j
⋆-var (var-wf {i} _ _) _ = i , refl
⋆-var (coh-wf _ _ _ _ _) ()
⋆-var (cst-wf {()} _ _)

tm-ctx : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢ctx
tm-ctx (var-wf w _)         = w
tm-ctx (coh-wf _ _ _ _ s)   = S.sub-ctx closed s
tm-ctx (cst-wf {()} _ _)

lookup-wf : ∀ {Γ i A} → Γ ⊢ctx → lookup Γ i ≡ just A → Γ ⊢ty A
lookup-wf {Γ ▸ B} {i} (▸-wf w b) eq with i ==ℕ len Γ
... | true  = subst (Γ ▸ B ⊢ty_) (just-inj eq) (wk-ty b (▸-wf w b))
  where
  just-inj : ∀ {x y : Ty} → just x ≡ just y → x ≡ y
  just-inj refl = refl
... | false = wk-ty (lookup-wf w eq) (▸-wf w b)

sub-len : ∀ {Γ τ k} → Γ ⊢sub τ ∶ chainC k → lenₛ τ ≡ vtx (suc k)
sub-len {k = k} s = trans (snd (S.sub-sc closed s)) (len-chain k)

-- Lookups below the last two entries.
lookupₛ-there₂ : ∀ σ x e i → i < lenₛ σ → lookupₛ (σ ,ₛ x ,ₛ e) i ≡ lookupₛ σ i
lookupₛ-there₂ σ x e i p =
  trans (lookupₛ-there (σ ,ₛ x) e i (≤-step p)) (lookupₛ-there σ x i p)

-- The type of the last edge of a chain substitution.
edge-ty : ∀ {Γ τ x k} → Γ ⊢sub τ ∶ chainC k →
          arr ⋆ (var (vtx k)) (var (vtx (suc k))) [ τ ,ₛ x ]ty ≡ arr ⋆ (lookupₛ τ (vtx k)) x
edge-ty {τ = τ} {x} {k} s =
  cong₂ (arr ⋆)
    (lookupₛ-there τ x (vtx k) (subst (vtx k <_) (sym (sub-len s)) (vtx-< ≤-refl)))
    (lookupₛ-here τ x (vtx (suc k)) (sym (sub-len s)))

------------------------------------------------------------------------
-- 1-dimensional coherences are over chains.

data CohV (Γ : Ctx) (a b : Tm) : Ctx → Ty → Sub → Set where
  cohV : ∀ k {τ} →
         chainC k ⊢ps → chainC k ⊢ctx → chainC k ⊢ty arr ⋆ (var 0) (var (vtx k)) →
         T (cattSide (chainC k) ⋆ (var 0) (var (vtx k))) →
         Γ ⊢sub τ ∶ chainC k →
         lookupₛ τ 0 ≡ a → lookupₛ τ (vtx k) ≡ b →
         CohV Γ a b (chainC k) (arr ⋆ (var 0) (var (vtx k))) τ

coh-view : ∀ {Γ Θ A τ B a b} → Γ ⊢tm coh Θ A τ ∶ B → B ≡ arr ⋆ a b → CohV Γ a b Θ A τ
coh-view (coh-wf {A = A} {t} {t'} {τ} p w a ok s) eq
  with ⋆-sub A τ (arr-inj₁ eq)
... | refl with a
...   | arr-wf dt dt' with ⋆-var dt refl | ⋆-var dt' refl
...     | j , refl | j' , refl with chain-side p ok
...       | k , refl , refl , refl = cohV k p w a ok s (arr-inj₂ eq) (arr-inj₃ eq)

-- The endpoints of a 1-cell are objects.
ends : ∀ {Γ u B x y} → Γ ⊢tm u ∶ B → B ≡ arr ⋆ (var x) (var y) →
       (Γ ⊢tm var x ∶ ⋆) × (Γ ⊢tm var y ∶ ⋆)
ends (var-wf w eq) refl with lookup-wf w eq
... | arr-wf dx dy = dx , dy
ends d@(coh-wf _ _ _ _ _) e with coh-view d e
... | cohV k _ _ _ _ s ex ey =
  subst (λ t → _ ⊢tm t ∶ ⋆) ex (S.lookup-sub closed (chainC-wf k) (lookup-vtx k 0 z≤n) s) ,
  subst (λ t → _ ⊢tm t ∶ ⋆) ey (S.lookup-sub closed (chainC-wf k) (lookup-vtx k k ≤-refl) s)
ends (cst-wf {()} _ _) _

-- The last object of a chain substitution is a variable.
last-var : ∀ {Γ τ k} → Γ ⊢sub τ ∶ chainC k → Σ Nat λ w → lookupₛ τ (vtx k) ≡ var w
last-var {k = k} s = ⋆-var (S.lookup-sub closed (chainC-wf k) (lookup-vtx k k ≤-refl) s) refl

------------------------------------------------------------------------
-- The path of a 1-cell is a walk from its source to its target.

walk-++ : ∀ {Γ x p z q y} → Walk Γ x p z → Walk Γ z q y → Walk Γ x (p ++ q) y
walk-++ nil        w = w
walk-++ (cons e v) w = cons e (walk-++ v w)

mutual
  walk : ∀ {Γ B x y} u → Γ ⊢tm u ∶ B → B ≡ arr ⋆ (var x) (var y) → Walk Γ x (path u) y
  walk (var e) (var-wf _ eq) refl = cons eq nil
  walk (coh Θ A τ) d eq with coh-view d eq
  ... | cohV k _ _ _ _ s ex ey = walkCh k τ s ex ey
  walk (cst ()) _ _

  walkCh : ∀ {Γ x y} k τ → Γ ⊢sub τ ∶ chainC k → lookupₛ τ 0 ≡ var x → lookupₛ τ (vtx k) ≡ var y →
           Walk Γ x (pathCh τ) y
  walkCh zero (⟨⟩ ,ₛ x₀) _ refl refl = nil
  walkCh zero (_ ,ₛ _ ,ₛ _) (,-wf () _) _ _
  walkCh (suc k) (τ ,ₛ x' ,ₛ e) (,-wf (,-wf s dx) de) ex ey with last-var s
  ... | w , lw =
    walk-++ (walkCh k τ s (trans (sym (lookupₛ-there₂ τ x' e 0 (zero< s))) ex) lw)
            (walk e de (trans (edge-ty s) (cong₂ (arr ⋆) lw (trans (sym last) ey))))
    where
    zero< : ∀ {Γ τ k} → Γ ⊢sub τ ∶ chainC k → 0 < lenₛ τ
    zero< s = subst (0 <_) (sym (sub-len s)) (s≤s z≤n)
    last : lookupₛ (τ ,ₛ x' ,ₛ e) (vtx (suc k)) ≡ x'
    last = trans (lookupₛ-there (τ ,ₛ x') e (vtx (suc k))
                    (subst (vtx (suc k) <_) (cong suc (sym (sub-len s))) ≤-refl))
                 (lookupₛ-here τ x' (vtx (suc k)) (sym (sub-len s)))

tgtOf-eq : ∀ {Γ e x z} → lookup Γ e ≡ just (arr ⋆ (var x) (var z)) → tgtOf Γ e ≡ z
tgtOf-eq {Γ} {e} eq with lookup Γ e
tgtOf-eq refl | .(just _) = refl

walk-end : ∀ {Γ x p y} → Walk Γ x p y → endOf Γ x p ≡ y
walk-end nil = refl
walk-end {Γ} (cons {e = e} {p = p} le w) =
  trans (cong (λ t → endOf Γ t p) (tgtOf-eq {Γ} le)) (walk-end w)

------------------------------------------------------------------------
-- Arithmetic on path lengths.

private
  swap : ∀ a b c → b + (a + c) ≡ (a + b) + c
  swap a b c = trans (sym (+-assoc b a c)) (cong (_+ c) (+-comm b a))

  antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
  antisym z≤n     z≤n     = refl
  antisym (s≤s a) (s≤s b) = cong suc (antisym a b)

  ¬suc≤ : ∀ {n} → suc n ≤ n → ⊥
  ¬suc≤ (s≤s p) = ¬suc≤ p

pathlen : ∀ τ e o → ∣ path e ∣ + (∣ pathCh τ ∣ + o) ≡ ∣ pathCh τ ++ path e ∣ + o
pathlen τ e o = trans (swap ∣ pathCh τ ∣ ∣ path e ∣ o) (cong (_+ o) (sym (∣++∣ (pathCh τ) (path e))))

zero< : ∀ {Γ τ k} → Γ ⊢sub τ ∶ chainC k → 0 < lenₛ τ
zero< s = subst (0 <_) (sym (sub-len s)) (s≤s z≤n)

last-obj : ∀ {Γ τ x e k} → Γ ⊢sub τ ∶ chainC k → lookupₛ (τ ,ₛ x ,ₛ e) (vtx (suc k)) ≡ x
last-obj {τ = τ} {x} {e} {k} s =
  trans (lookupₛ-there (τ ,ₛ x) e (vtx (suc k))
           (subst (vtx (suc k) <_) (cong suc (sym (sub-len s))) ≤-refl))
        (lookupₛ-here τ x (vtx (suc k)) (sym (sub-len s)))

------------------------------------------------------------------------
-- The lift: lengths and end points.

lift-lk : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k →
          (lenₛ (liftCh τ o) ≡ lenₛ τ) × (lookupₛ (liftCh τ o) 0 ≡ var (vtx o)) ×
          (lookupₛ (liftCh τ o) (vtx k) ≡ var (vtx (∣ pathCh τ ∣ + o)))
lift-lk zero (⟨⟩ ,ₛ x) o _ = refl , refl , refl
lift-lk zero (_ ,ₛ _ ,ₛ _) o (,-wf () _)
lift-lk (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) _) =
  let (l , l0 , lk) = lift-lk k τ o s
      lτ = liftCh τ o
      v  = var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
      ln = trans l (sub-len s) in
  cong (λ n → suc (suc n)) l ,
  trans (lookupₛ-there₂ lτ v (lift e (∣ pathCh τ ∣ + o)) 0 (subst (0 <_) (sym ln) (s≤s z≤n))) l0 ,
  trans (lookupₛ-there (lτ ,ₛ v) _ (vtx (suc k)) (subst (vtx (suc k) <_) (cong suc (sym ln)) ≤-refl))
   (trans (lookupₛ-here lτ v (vtx (suc k)) (sym ln))
          (cong (λ n → var (vtx n)) (pathlen τ e o)))

------------------------------------------------------------------------
-- The lift is well typed.

mutual
  lift-ty : ∀ {Γ B a b K} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → ∣ path u ∣ + o ≤ K →
            chainC K ⊢tm lift u o ∶ arr ⋆ (var (vtx o)) (var (vtx (∣ path u ∣ + o)))
  lift-ty {K = K} (var e) o _ _ le = var-wf (chainC-wf K) (lookup-edge K o le)
  lift-ty {K = K} (coh Θ A τ) o d eq le with coh-view d eq
  ... | cohV k p w a ok s _ _ =
    let (_ , l0 , lk) = lift-lk k τ o s in
    subst (chainC K ⊢tm lift (coh Θ A τ) o ∶_) (cong₂ (arr ⋆) l0 lk)
          (coh-wf p w a ok (liftCh-ty k τ o s le))
  lift-ty (cst ()) _ _ _ _

  liftCh-ty : ∀ {Γ K} k τ o → Γ ⊢sub τ ∶ chainC k → ∣ pathCh τ ∣ + o ≤ K →
              chainC K ⊢sub liftCh τ o ∶ chainC k
  liftCh-ty {K = K} zero (⟨⟩ ,ₛ x) o _ le =
    ,-wf (⟨⟩-wf (chainC-wf K)) (var-wf (chainC-wf K) (lookup-vtx K o le))
  liftCh-ty zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _
  liftCh-ty {K = K} (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) de) le =
    ,-wf (,-wf sτ (var-wf wK (lookup-vtx K (n₂ + o') le₂)))
         (subst (chainC K ⊢tm lift e o' ∶_)
                (sym (trans (edge-ty sτ) (cong (λ t → arr ⋆ t (var (vtx (n₂ + o')))) lk)))
                (lift-ty e o' de refl le₂))
    where
    wK = chainC-wf K
    n₁ = ∣ pathCh τ ∣
    n₂ = ∣ path e ∣
    o' = n₁ + o
    le₂ : n₂ + o' ≤ K
    le₂ = subst (_≤ K) (sym (pathlen τ e o)) le
    le₁ : o' ≤ K
    le₁ = ≤-trans (≤-+l n₂ o') le₂
    sτ = liftCh-ty k τ o s le₁
    lk = snd (snd (lift-lk k τ o s))

------------------------------------------------------------------------
-- Substituting σ back into the lift gives the original term.

Seg : Ctx → Sub → Nat → Nat → List Nat → Set
Seg Γ σ o x []      = lookupₛ σ (vtx o) ≡ var x
Seg Γ σ o x (e ∷ p) = (lookupₛ σ (vtx o) ≡ var x) × (lookupₛ σ (edge (suc o)) ≡ var e) ×
                      Seg Γ σ (suc o) (tgtOf Γ e) p

seg-head : ∀ {Γ σ o x} p → Seg Γ σ o x p → lookupₛ σ (vtx o) ≡ var x
seg-head []      h       = h
seg-head (_ ∷ _) (h , _) = h

seg-end : ∀ {Γ σ o x} p → Seg Γ σ o x p → lookupₛ σ (vtx (∣ p ∣ + o)) ≡ var (endOf Γ x p)
seg-end []      h = h
seg-end {Γ} {σ} {o} (e ∷ p) (_ , _ , h) =
  subst (λ n → lookupₛ σ (vtx n) ≡ var (endOf Γ (tgtOf Γ e) p)) (+-suc ∣ p ∣ o) (seg-end p h)

seg-split : ∀ {Γ σ o x} p q → Seg Γ σ o x (p ++ q) →
            Seg Γ σ o x p × Seg Γ σ (∣ p ∣ + o) (endOf Γ x p) q
seg-split []      q h = seg-head q h , h
seg-split {Γ} {σ} {o} (e ∷ p) q (h , he , r) =
  let (a , b) = seg-split p q r in
  (h , he , a) , subst (λ n → Seg Γ σ n (endOf Γ (tgtOf Γ e) p) q) (+-suc ∣ p ∣ o) b

mutual
  lift-sub : ∀ {Γ B x y σ} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ (var x) (var y) →
             Seg Γ σ o x (path u) → lift u o [ σ ]tm ≡ u
  lift-sub (var e) o _ _ (_ , he , _) = he
  lift-sub (coh Θ A τ) o d eq sg with coh-view d eq
  ... | cohV k _ _ _ _ s ex _ = cong (coh Θ A) (liftCh-sub k τ o s ex sg)
  lift-sub (cst ()) _ _ _ _

  liftCh-sub : ∀ {Γ x σ} k τ o → Γ ⊢sub τ ∶ chainC k → lookupₛ τ 0 ≡ var x →
               Seg Γ σ o x (pathCh τ) → liftCh τ o ∘ σ ≡ τ
  liftCh-sub zero (⟨⟩ ,ₛ x₀) o _ ex sg = cong (⟨⟩ ,ₛ_) (trans sg (sym ex))
  liftCh-sub zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _ _
  liftCh-sub {Γ} {x} {σ} (suc k) (τ ,ₛ x' ,ₛ e) o (,-wf (,-wf s dx) de) ex sg
    with last-var s | ⋆-var dx refl
  ... | w , lw | z , refl =
    cong₃ (λ a b c → a ,ₛ b ,ₛ c) (liftCh-sub k τ o s ex' sg₁) obj (lift-sub e o' de eqe sg₂)
    where
    o' = ∣ pathCh τ ∣ + o
    ex' : lookupₛ τ 0 ≡ var x
    ex' = trans (sym (lookupₛ-there₂ τ (var z) e 0 (zero< s))) ex
    wk : endOf Γ x (pathCh τ) ≡ w
    wk = walk-end (walkCh k τ s ex' lw)
    eqe : arr ⋆ (var (vtx k)) (var (vtx (suc k))) [ τ ,ₛ var z ]ty ≡ arr ⋆ (var w) (var z)
    eqe = trans (edge-ty s) (cong (λ t → arr ⋆ t (var z)) lw)
    halves = seg-split (pathCh τ) (path e) sg
    sg₁ = fst halves
    sg₂ : Seg Γ σ o' w (path e)
    sg₂ = subst (λ t → Seg Γ σ o' t (path e)) wk (snd halves)
    obj : lookupₛ σ (vtx (∣ path e ∣ + o')) ≡ var z
    obj = trans (seg-end (path e) sg₂) (cong var (walk-end (walk e de eqe)))

------------------------------------------------------------------------
-- σ is well typed and lies along the walk.

wgo-ty : ∀ {Γ j σ x p y} → Γ ⊢sub σ ∶ chainC j → lookupₛ σ (vtx j) ≡ var x →
         Walk Γ x p y → Γ ⊢sub wgo Γ σ x p ∶ chainC (∣ p ∣ + j)
wgo-ty s lx nil = s
wgo-ty {Γ} {j} {σ} {x} (s) lx (cons {z = z} {e = e} {p = p} le w)
  with lookup-wf (S.sub-ctx closed s) le
... | arr-wf _ dz =
  subst (λ t → Γ ⊢sub wgo Γ (σ ,ₛ var t ,ₛ var e) t p ∶ chainC (suc (∣ p ∣ + j)))
        (sym (tgtOf-eq {Γ} le))
        (subst (λ n → Γ ⊢sub wgo Γ (σ ,ₛ var z ,ₛ var e) z p ∶ chainC n) (+-suc ∣ p ∣ j)
               (wgo-ty s₁ (last-obj s) w))
  where
  wΓ = S.sub-ctx closed s
  s₁ : Γ ⊢sub σ ,ₛ var z ,ₛ var e ∶ chainC (suc j)
  s₁ = ,-wf (,-wf s dz)
            (subst (Γ ⊢tm var e ∶_)
                   (sym (trans (edge-ty s) (cong (λ t → arr ⋆ t (var z)) lx)))
                   (var-wf wΓ le))

wgo-keep : ∀ {Γ} σ x p i → i < lenₛ σ → lookupₛ (wgo Γ σ x p) i ≡ lookupₛ σ i
wgo-keep σ x []      i h = refl
wgo-keep {Γ} σ x (e ∷ p) i h =
  trans (wgo-keep (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p i (≤-step (≤-step h)))
        (lookupₛ-there₂ σ _ _ i h)

wgo-seg : ∀ {Γ j σ x} p → lenₛ σ ≡ vtx (suc j) → lookupₛ σ (vtx j) ≡ var x →
          Seg Γ (wgo Γ σ x p) j x p
wgo-seg []          l lx = lx
wgo-seg {Γ} {j} {σ} (e ∷ p) l lx =
  trans (wgo-keep σ₁ t p (vtx j) (≤-step (≤-step bj))) (trans (lookupₛ-there₂ σ _ _ (vtx j) bj) lx) ,
  trans (wgo-keep σ₁ t p (edge (suc j)) (s≤s (subst (edge (suc j) ≤_) (cong suc (sym l)) ≤-refl)))
        (lookupₛ-here (σ ,ₛ var t) (var e) (edge (suc j)) (cong suc (sym l))) ,
  wgo-seg p (cong (λ n → suc (suc n)) l)
    (trans (lookupₛ-there (σ ,ₛ var t) (var e) (vtx (suc j))
              (subst (vtx (suc j) <_) (cong suc (sym l)) ≤-refl))
           (lookupₛ-here σ (var t) (vtx (suc j)) (sym l)))
  where
  t  = tgtOf Γ e
  σ₁ = σ ,ₛ var t ,ₛ var e
  bj : vtx j < lenₛ σ
  bj = subst (vtx j <_) (sym l) (vtx-< ≤-refl)

------------------------------------------------------------------------
-- Full support: the lift of a 1-cell uses every level of its segment
-- of the chain, except possibly its two end objects (which its type
-- uses).

-- The levels of the segment of length n starting at x_o.
InSeg : Nat → Nat → Nat → Set
InSeg o n m =
  (Σ Nat λ j → (o ≤ j) × (j ≤ n + o) × (m ≡ vtx j)) ⊎
  (Σ Nat λ j → (o ≤ j) × (j < n + o) × (m ≡ edge (suc j)))

inseg-split : ∀ n₁ n₂ o m → InSeg o (n₁ + n₂) m → InSeg o n₁ m ⊎ InSeg (n₁ + o) n₂ m
inseg-split n₁ n₂ o m (inj₁ (j , oj , jle , e)) with ≤-total j (n₁ + o)
... | inj₁ q = inj₁ (inj₁ (j , oj , q , e))
... | inj₂ q = inj₂ (inj₁ (j , ≤-trans (≤-step ≤-refl) q ,
                           subst (j ≤_) (sym (swap n₁ n₂ o)) jle , e))
inseg-split n₁ n₂ o m (inj₂ (j , oj , jlt , e)) with ≤-total (suc j) (n₁ + o)
... | inj₁ q = inj₁ (inj₂ (j , oj , q , e))
... | inj₂ q = inj₂ (inj₂ (j , ≤-pred q , subst (suc j ≤_) (sym (swap n₁ n₂ o)) jlt , e))

lookup-fv : ∀ σ i {m} → i < lenₛ σ → lookupₛ σ i ≡ var m → m ∈ fvSub σ
lookup-fv (σ ,ₛ t) i {m} (s≤s h) eq with ≤-case h
... | inj₁ q = ∈-++l (fvSub σ) (fvTm t)
                 (lookup-fv σ i q (trans (sym (lookupₛ-there σ t i q)) eq))
... | inj₂ q = ∈-++r (fvSub σ) (fvTm t)
                 (subst (λ u → m ∈ fvTm u) (sym (trans (sym (lookupₛ-here σ t i q)) eq)) (∈-here m []))

mutual
  lift-fs : ∀ {Γ B a b} u o → Γ ⊢tm u ∶ B → B ≡ arr ⋆ a b → ∀ m → InSeg o ∣ path u ∣ m →
            (m ∈ fvTm (lift u o)) ⊎ (m ≡ vtx o ⊎ m ≡ vtx (∣ path u ∣ + o))
  lift-fs (var e) o _ _ m (inj₁ (j , oj , jle , refl)) with ≤-suc-case jle
  ... | inj₁ q    = inj₂ (inj₁ (cong vtx (antisym q oj)))
  ... | inj₂ refl = inj₂ (inj₂ refl)
  lift-fs (var e) o _ _ m (inj₂ (j , oj , s≤s jlt , refl)) with antisym jlt oj
  ... | refl = inj₁ (∈-here (edge (suc j)) [])
  lift-fs (coh Θ A τ) o d eq m h with coh-view d eq
  ... | cohV k _ _ _ _ s _ _ = inj₁ (liftCh-fs k τ o s m h)
  lift-fs (cst ()) _ _ _ _ _

  liftCh-fs : ∀ {Γ} k τ o → Γ ⊢sub τ ∶ chainC k → ∀ m → InSeg o ∣ pathCh τ ∣ m →
              m ∈ fvSub (liftCh τ o)
  liftCh-fs zero (⟨⟩ ,ₛ x) o _ m (inj₁ (j , oj , jle , refl)) with antisym oj jle
  ... | refl = ∈-here (vtx j) []
  liftCh-fs zero (⟨⟩ ,ₛ x) o _ m (inj₂ (j , oj , jlt , _)) = ⊥-elim (¬suc≤ (≤-trans jlt oj))
  liftCh-fs zero (_ ,ₛ _ ,ₛ _) o (,-wf () _) _ _
  liftCh-fs (suc k) (τ ,ₛ x ,ₛ e) o (,-wf (,-wf s _) de) m h
    with inseg-split ∣ pathCh τ ∣ ∣ path e ∣ o m
           (subst (λ n → InSeg o n m) (∣++∣ (pathCh τ) (path e)) h)
  ... | inj₁ h₁ = ∈-++l (fvSub lτ ++ fvTm v) (fvTm le)
                    (∈-++l (fvSub lτ) (fvTm v) (liftCh-fs k τ o s m h₁))
    where
    lτ = liftCh τ o
    v  = var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
    le = lift e (∣ pathCh τ ∣ + o)
  ... | inj₂ h₂ with lift-fs e (∣ pathCh τ ∣ + o) de refl m h₂
  ...   | inj₁ q = ∈-++r (fvSub lτ ++ fvTm v) (fvTm le) q
    where
    lτ = liftCh τ o
    v  = var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
    le = lift e (∣ pathCh τ ∣ + o)
  ...   | inj₂ (inj₁ refl) =
    ∈-++l (fvSub lτ ++ fvTm v) (fvTm le) (∈-++l (fvSub lτ) (fvTm v)
      (lookup-fv lτ (vtx k)
         (subst (vtx k <_) (sym (trans (fst (lift-lk k τ o s)) (sub-len s))) (vtx-< ≤-refl))
         (snd (snd (lift-lk k τ o s)))))
    where
    lτ = liftCh τ o
    v  = var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
    le = lift e (∣ pathCh τ ∣ + o)
  ...   | inj₂ (inj₂ refl) =
    ∈-++l (fvSub lτ ++ fvTm v) (fvTm le) (∈-++r (fvSub lτ) (fvTm v) (∈-here (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o))) []))
    where
    lτ = liftCh τ o
    v  = var (vtx (∣ path e ∣ + (∣ pathCh τ ∣ + o)))
    le = lift e (∣ pathCh τ ∣ + o)

-- Every level of Θ_k is in the segment of length k from x₀.
private
  dbl-inv : ∀ a b → dbl a ≤ dbl b → a ≤ b
  dbl-inv zero    b       _ = z≤n
  dbl-inv (suc a) (suc b) (s≤s (s≤s p)) = s≤s (dbl-inv a b p)

  dbl-inv-s : ∀ a b → dbl a ≤ suc (dbl b) → a ≤ b
  dbl-inv-s zero    b       _ = z≤n
  dbl-inv-s (suc a) (suc b) (s≤s (s≤s p)) = s≤s (dbl-inv-s a b p)
  dbl-inv-s (suc a) zero    (s≤s ())

  vtx-inv : ∀ j k → vtx j < vtx (suc k) → j ≤ k
  vtx-inv zero    k       _ = z≤n
  vtx-inv (suc j) (suc k) (s≤s (s≤s p)) = s≤s (dbl-inv-s j k p)
  vtx-inv (suc j) zero    (s≤s ())

  edge-inv : ∀ j k → edge (suc j) < vtx (suc k) → j < k
  edge-inv j (suc k) (s≤s (s≤s (s≤s p))) = s≤s (dbl-inv j k p)
  edge-inv j zero    (s≤s ())

inseg-all : ∀ k m → m < vtx (suc k) → InSeg 0 k m
inseg-all k m h with parity m
... | isVtx j  = inj₁ (j , z≤n , subst (j ≤_) (sym (+-zero k)) (vtx-inv j k h) , refl)
... | isEdge j = inj₂ (j , z≤n , subst (suc j ≤_) (sym (+-zero k)) (edge-inv j k h) , refl)

-- Free variables of scoped syntax are in scope.
mutual
  sc-fv : ∀ n t {m} → S.ScTm n t → m ∈ fvTm t → m < n
  sc-fv n (var i) {m} h mem = subst (_< n) (sym (∈-single mem)) (T→< i n h)
  sc-fv n (coh _ _ σ) h mem = sc-fvs n σ h mem
  sc-fv n (cst ()) _ _

  sc-fvs : ∀ n σ {m} → S.ScSub n σ → m ∈ fvSub σ → m < n
  sc-fvs n (σ ,ₛ t) (hσ , ht) mem with ∈-++ (fvSub σ) (fvTm t) mem
  ... | inj₁ q = sc-fvs n σ hσ q
  ... | inj₂ q = sc-fv n t ht q

downFrom-mem : ∀ {m} n → m ∈ downFrom n → m < n
downFrom-mem {m} (suc n) mem with ∨-elim (m ==ℕ n) mem
... | inj₁ q = subst (λ x → x < suc n) (sym (==ℕ-sound m n q)) ≤-refl
... | inj₂ q = ≤-step (downFrom-mem n q)

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

-- The side condition of the filler: full coherence.
fs-cell : ∀ {Γ t a b} → Γ ⊢tm t ∶ arr ⋆ (var a) (var b) →
          T (≈? (fvTmTy (lift t 0) (arr ⋆ (var 0) (var (vtx ∣ path t ∣))))
                (downFrom (len (chainC ∣ path t ∣))))
fs-cell {t = t} d =
  ∧-intro (all-intro (λ x → elem x ys) xs (λ m mem → elem-downFrom (bound m mem)))
          (all-intro (λ x → elem x xs) ys (λ m mem → cover m (downFrom-mem (len (chainC k)) mem)))
  where
  k  = ∣ path t ∣
  ũ  = lift t 0
  xs = fvTmTy ũ (arr ⋆ (var 0) (var (vtx k)))
  ys = downFrom (len (chainC k))
  tyũ : chainC k ⊢tm ũ ∶ arr ⋆ (var 0) (var (vtx (k + 0)))
  tyũ = lift-ty t 0 d refl (subst (_≤ k) (sym (+-zero k)) ≤-refl)
  inLen : ∀ {m} → m < vtx (suc k) → m < len (chainC k)
  inLen {m} = subst (m <_) (sym (len-chain k))
  bound : ∀ m → m ∈ xs → m < len (chainC k)
  bound m mem with ∈-++ (fvTm ũ) (0 ∷ vtx k ∷ []) mem
  ... | inj₁ q = sc-fv (len (chainC k)) ũ (S.tm-sc closed tyũ) q
  ... | inj₂ q with ∨-elim (m ==ℕ 0) q
  ...   | inj₁ r = inLen (subst (_< vtx (suc k)) (sym (==ℕ-sound m 0 r)) (vtx-< (z≤n {k})))
  ...   | inj₂ r = inLen (subst (_< vtx (suc k)) (sym (∈-single {m} r)) (vtx-< ≤-refl))
  cover : ∀ m → m < len (chainC k) → m ∈ xs
  cover m h with lift-fs t 0 d refl m (inseg-all k m (subst (m <_) (len-chain k) h))
  ... | inj₁ q         = ∈-++l (fvTm ũ) _ q
  ... | inj₂ (inj₁ q)  = ∈-++r (fvTm ũ) (0 ∷ vtx k ∷ []) (subst (_∈ 0 ∷ vtx k ∷ []) (sym q) (∈-here 0 (vtx k ∷ [])))
  ... | inj₂ (inj₂ q)  = ∈-++r (fvTm ũ) (0 ∷ vtx k ∷ [])
                           (∈-there {m} 0 (vtx k ∷ [])
                             (subst (_∈ vtx k ∷ []) (sym (trans q (cong vtx (+-zero k)))) (∈-here (vtx k) [])))

------------------------------------------------------------------------
-- The theorem.

total : ∀ {Γ u v a b} →
        Γ ⊢tm u ∶ arr ⋆ (var a) (var b) → Γ ⊢tm v ∶ arr ⋆ (var a) (var b) →
        path u ≡ path v →
        Γ ⊢tm fill₁ Γ u v (arr ⋆ (var a) (var b)) ∶ arr (arr ⋆ (var a) (var b)) u v
total {Γ} {u} {v} {a} {b} du dv pe =
  subst (Γ ⊢tm fill₁ Γ u v (arr ⋆ (var a) (var b)) ∶_) tyEq
    (coh-wf (ps (chainC-ps k)) (chainC-wf k) (arr-wf tu tv)
            (∨-inl (isOp (chainC k) A' (lift u 0) (lift v 0)) (∧-intro (fs-cell du) fsv)) sσ)
  where
  p  = path u
  k  = ∣ p ∣
  A' = arr ⋆ (var 0) (var (vtx k))
  σ  = wsub Γ a p
  k≤ : ∀ n → n ≡ k → n + 0 ≤ k
  k≤ n e = subst (_≤ k) (sym (trans (+-zero n) e)) ≤-refl
  tu : chainC k ⊢tm lift u 0 ∶ A'
  tu = subst (λ n → chainC k ⊢tm lift u 0 ∶ arr ⋆ (var 0) (var (vtx n))) (+-zero k)
             (lift-ty u 0 du refl (k≤ k refl))
  eqv : ∣ path v ∣ ≡ k
  eqv = cong ∣_∣ (sym pe)
  tv : chainC k ⊢tm lift v 0 ∶ A'
  tv = subst (λ n → chainC k ⊢tm lift v 0 ∶ arr ⋆ (var 0) (var (vtx n))) (trans (+-zero _) eqv)
             (lift-ty v 0 dv refl (k≤ ∣ path v ∣ eqv))
  fsv : T (≈? (fvTmTy (lift v 0) A') (downFrom (len (chainC k))))
  fsv = subst (λ n → T (≈? (fvTmTy (lift v 0) (arr ⋆ (var 0) (var (vtx n)))) (downFrom (len (chainC n)))))
              eqv (fs-cell dv)
  wk : Walk Γ a p b
  wk = walk u du refl
  sσ : Γ ⊢sub σ ∶ chainC k
  sσ = subst (λ n → Γ ⊢sub σ ∶ chainC n) (+-zero k)
             (wgo-ty (,-wf (⟨⟩-wf (tm-ctx du)) (fst (ends du refl))) refl wk)
  sg : Seg Γ σ 0 a p
  sg = wgo-seg p refl refl
  tyEq : arr A' (lift u 0) (lift v 0) [ σ ]ty ≡ arr (arr ⋆ (var a) (var b)) u v
  tyEq = cong₃ arr
    (cong₂ (arr ⋆) (seg-head p sg)
      (trans (cong (λ n → lookupₛ σ (vtx n)) (sym (+-zero k)))
        (trans (seg-end p sg) (cong var (walk-end wk)))))
    (lift-sub u 0 du refl sg)
    (lift-sub v 0 dv refl (subst (Seg Γ σ 0 a) pe sg))
