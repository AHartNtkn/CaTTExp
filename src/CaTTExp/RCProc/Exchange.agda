------------------------------------------------------------------------
-- The exchange coherence over the two-disc context (ledger S20 (i),
-- stage 3e, Lemma E part (1); notes/relative-coherence.md §2).
--
-- E m k n is the pasting context of the tree
--
--   node (leaves m ++ col ∷ leaves k ++ col ∷ leaves n),
--
-- a chain of m edges (λ), a 2-disc Z₁ : f₁ ⇒ f₁′, a chain of k edges
-- (μ), a 2-disc Z₂ : f₂ ⇒ f₂′ and a chain of n edges (ρ), from 0 to b.
-- With the strong order of E (`TwoPathFacts.key2-ps`) and its 2-path
-- terms (`TwoPathTerm.Term`), the two orders of firing Z₁ and Z₂,
--
--   P = [ wg λ Z₁ (μ ++ f₂ ∷ ρ) , wg (λ ++ f₁′ ∷ μ) Z₂ ρ ]
--   Q = [ wg (λ ++ f₁ ∷ μ) Z₂ ρ , wg λ Z₁ (μ ++ f₂′ ∷ ρ) ]
--
-- give 2-cells L = term P and R = term Q of E, both from B E 0 S to
-- B E 0 T, where S = λ ++ f₁ ∷ μ ++ f₂ ∷ ρ and T = λ ++ f₁′ ∷ μ ++ f₂′ ∷ ρ
-- (`L-wf`, `R-wf`). Both are full: every variable of E is an endpoint
-- or edge of S or T, or Z₁ or Z₂, which L and R contain (`full-L`,
-- `full-R`). So
--
--   coh E (arr A (arr L R)) θ  and  coh E (arr A (arr R L)) θ
--
-- are well-typed coherences for every Γ ⊢ θ : E (`xch-wf`, `xch-wf′`):
-- the exchange 3-cells L ⇄ R, pulled back along θ.
--
-- Not here: relating L[θ] and R[θ] to the 2-path terms of Γ for an
-- exchange step of Γ (part (2), which needs Lemma G).
------------------------------------------------------------------------
module CaTTExp.RCProc.Exchange where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (tm-ty; ps-wf; sphSub)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.GraphFillerTotal using (Walk; nil; cons; wgo; wsub; tgtOf; tgtOf-eq; walk-++; sc-fv; downFrom-mem)
open import CaTTExp.GraphFillerTotal.Chains
  using (_≤_; z≤n; s≤s; _<_; ≤-case; _⊎_; inj₁; inj₂; _∈_; ∈-here; ∈-there; ∈-++l; ∈-++r; ∈-++; ∨-elim; all-intro; elem-downFrom)
open import CaTTExp.PsRaise using (Raised)
open import CaTTExp.RCProc.Column
open import CaTTExp.RCProc.Path1 using (B)
open import CaTTExp.RCProc.Eg using (vcomp; eg; module EgTm)
open import CaTTExp.RCProc.TwoPathCtx using (Key2Ctx; Var2)
open import CaTTExp.RCProc.TwoPathFacts using (key2-ps; srcVar-eq; tgtVar-eq)
open import CaTTExp.RCProc.Key2Bd using (key2-bdok)
open import CaTTExp.RCProc.TwoPathTerm using (module Term)

------------------------------------------------------------------------
-- Lists.

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

++-assoc : ∀ (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

private
  ∈-cons : ∀ {m} x xs → m ∈ x ∷ xs → (m ≡ x) ⊎ (m ∈ xs)
  ∈-cons {m} x xs p with ∨-elim (m ==ℕ x) p
  ... | inj₁ q = inj₁ (==ℕ-sound m x q)
  ... | inj₂ q = inj₂ q

  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

------------------------------------------------------------------------
-- Context extension.

Ext : Ctx → Ctx → Set
Ext Γ Δ = ∀ {i A} → lookup Γ i ≡ just A → lookup Δ i ≡ just A

ext-∘ : ∀ {Γ Δ Θ} → Ext Γ Δ → Ext Δ Θ → Ext Γ Θ
ext-∘ e f l = f (e l)

ext-chain : ∀ Γ x n → Ext Γ (chainFrom Γ x n)
ext-chain Γ x zero    l = l
ext-chain Γ x (suc n) {i} l =
  ext-chain (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n
    (lookup-wk (Γ ▸ ⋆) i (arr ⋆ (var x) (var (len Γ))) (lookup-wk Γ i ⋆ l))

ext-raised : ∀ Δ x A → Ext Δ (Raised Δ x A)
ext-raised Δ x A {i} l =
  lookup-wk (Δ ▸ A ▸ F ▸ F) i Z (lookup-wk (Δ ▸ A ▸ F) i F (lookup-wk (Δ ▸ A) i F (lookup-wk Δ i A l)))
  where
  F = arr A (var x) (var (len Δ))
  Z = arr F (var (suc (len Δ))) (var (suc (suc (len Δ))))

walk-ext : ∀ {Γ Δ x p y} → Ext Γ Δ → Walk Γ x p y → Walk Δ x p y
walk-ext e nil        = nil
walk-ext e (cons l w) = cons (e l) (walk-ext e w)

------------------------------------------------------------------------
-- Chains: their edges, walk and lookups.

-- The edges of chainFrom Γ x n, with L = len Γ.
chEdges : Nat → Nat → List Nat
chEdges L zero    = []
chEdges L (suc n) = suc L ∷ chEdges (suc (suc L)) n

walk-chain : ∀ Γ x n → Walk (chainFrom Γ x n) x (chEdges (len Γ) n) (endFrom Γ x n)
walk-chain Γ x zero    = nil
walk-chain Γ x (suc n) =
  cons (ext-chain Γ′ (len Γ) n (lookup-top (Γ ▸ ⋆) (arr ⋆ (var x) (var (len Γ)))))
       (walk-chain Γ′ (len Γ) n)
  where Γ′ = Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))

-- A chain edge e ends at the point e − 1.
lk-chain : ∀ Γ x n e → e ∈ chEdges (len Γ) n →
           Σ Nat λ u → lookup (chainFrom Γ x n) e ≡ just (arr ⋆ (var u) (var (pred e)))
lk-chain Γ x (suc n) e q with ∈-cons (suc (len Γ)) (chEdges (suc (suc (len Γ))) n) q
... | inj₁ refl = x , ext-chain Γ′ (len Γ) n (lookup-top (Γ ▸ ⋆) (arr ⋆ (var x) (var (len Γ))))
  where Γ′ = Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))
... | inj₂ r = lk-chain (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n e r

------------------------------------------------------------------------
-- The disc of a raised context.

module Disc (Δ : Ctx) (x : Nat) where
  L : Nat
  L = len Δ

  F : Ty
  F = arr ⋆ (var x) (var L)

  D : Ctx
  D = Raised Δ x ⋆

  Zt : Ty
  Zt = arr F (var (suc L)) (var (suc (suc L)))

  lk-f : lookup D (suc L) ≡ just F
  lk-f = lookup-wk (Δ ▸ ⋆ ▸ F ▸ F) (suc L) Zt (lookup-wk (Δ ▸ ⋆ ▸ F) (suc L) F (lookup-top (Δ ▸ ⋆) F))

  lk-f′ : lookup D (suc (suc L)) ≡ just F
  lk-f′ = lookup-wk (Δ ▸ ⋆ ▸ F ▸ F) (suc (suc L)) Zt (lookup-top (Δ ▸ ⋆ ▸ F) F)

  lk-Z : lookup D (suc (suc (suc L))) ≡ just (arr F (var (suc L)) (var (suc (suc L))))
  lk-Z = lookup-top (Δ ▸ ⋆ ▸ F ▸ F) Zt

------------------------------------------------------------------------
-- Covering a context by a set of variables.

Cov : Ctx → List Nat → Set
Cov Γ X = ∀ {m} → m < len Γ → m ∈ X

cov-▸ : ∀ Γ A X → Cov Γ X → len Γ ∈ X → Cov (Γ ▸ A) X
cov-▸ Γ A X c h (s≤s p) with ≤-case p
... | inj₁ q    = c q
... | inj₂ refl = h

cov-chain : ∀ Γ x n X → Cov Γ X → (∀ e → e ∈ chEdges (len Γ) n → (e ∈ X) × (pred e ∈ X)) →
            Cov (chainFrom Γ x n) X
cov-chain Γ x zero    X c h = c
cov-chain Γ x (suc n) X c h =
  cov-chain (Γ ▸ ⋆ ▸ arr ⋆ (var x) (var (len Γ))) (len Γ) n X
    (cov-▸ (Γ ▸ ⋆) (arr ⋆ (var x) (var (len Γ))) X (cov-▸ Γ ⋆ X c (snd h₀)) (fst h₀))
    (λ e q → h e (∈-there {e} (suc (len Γ)) (chEdges (suc (suc (len Γ))) n) q))
  where h₀ = h (suc (len Γ)) (∈-here (suc (len Γ)) (chEdges (suc (suc (len Γ))) n))

cov-raised : ∀ Δ x X → Cov Δ X → len Δ ∈ X → suc (len Δ) ∈ X → suc (suc (len Δ)) ∈ X →
             suc (suc (suc (len Δ))) ∈ X → Cov (Raised Δ x ⋆) X
cov-raised Δ x X c h₀ h₁ h₂ h₃ = cov-▸ (Δ ▸ ⋆ ▸ F ▸ F) Z X (cov-▸ (Δ ▸ ⋆ ▸ F) F X (cov-▸ (Δ ▸ ⋆) F X (cov-▸ Δ ⋆ X c h₀) h₁) h₂) h₃
  where
  F = arr ⋆ (var x) (var (len Δ))
  Z = arr F (var (suc (len Δ))) (var (suc (suc (len Δ))))

------------------------------------------------------------------------
-- Free variables.

private
  fv-wgo-σ : ∀ Γ σ x p {m} → m ∈ fvSub σ → m ∈ fvSub (wgo Γ σ x p)
  fv-wgo-σ Γ σ x []      q = q
  fv-wgo-σ Γ σ x (e ∷ p) {m} q =
    fv-wgo-σ Γ (σ ,ₛ var (tgtOf Γ e) ,ₛ var e) (tgtOf Γ e) p
      (∈-++l (fvSub σ ++ (tgtOf Γ e ∷ [])) (e ∷ []) (∈-++l (fvSub σ) (tgtOf Γ e ∷ []) q))

-- The edges of a walk and their targets are variables of its
-- substitution.
fv-wgo : ∀ Γ σ x p e → e ∈ p → (e ∈ fvSub (wgo Γ σ x p)) × (tgtOf Γ e ∈ fvSub (wgo Γ σ x p))
fv-wgo Γ σ x (e′ ∷ p) e q with ∈-cons e′ p q
... | inj₁ refl =
  fv-wgo-σ Γ σ′ (tgtOf Γ e) p (∈-++r (fvSub σ ++ (tgtOf Γ e ∷ [])) (e ∷ []) (∈-here e [])) ,
  fv-wgo-σ Γ σ′ (tgtOf Γ e) p (∈-++l (fvSub σ ++ (tgtOf Γ e ∷ [])) (e ∷ [])
                                (∈-++r (fvSub σ) (tgtOf Γ e ∷ []) (∈-here (tgtOf Γ e) [])))
  where σ′ = σ ,ₛ var (tgtOf Γ e) ,ₛ var e
... | inj₂ r = fv-wgo Γ (σ ,ₛ var (tgtOf Γ e′) ,ₛ var e′) (tgtOf Γ e′) p e r

fv-vcomp-c : ∀ A t s u c h {m} → m ∈ fvTm c → m ∈ fvTm (vcomp A t s u c h)
fv-vcomp-c A t s u c h q =
  ∈-++l ((fvSub sp ++ fvTm c) ++ fvTm u) (fvTm h)
    (∈-++l (fvSub sp ++ fvTm c) (fvTm u) (∈-++r (fvSub sp) (fvTm c) q))
  where sp = sphSub (arr A t s)

fv-vcomp-h : ∀ A t s u c h {m} → m ∈ fvTm h → m ∈ fvTm (vcomp A t s u c h)
fv-vcomp-h A t s u c h q = ∈-++r ((fvSub (sphSub (arr A t s)) ++ fvTm c) ++ fvTm u) (fvTm h) q

-- The cell e_g contains its generator.
fv-eg : ∀ Γ a λ′ w s t x ρ b Ps Pt → x ∈ fvTm (eg Γ a λ′ w s t x ρ b Ps Pt)
fv-eg Γ a λ′ w s t x ρ b Ps Pt =
  fv-vcomp-h A Bs c⁻θ Bt κ₁ (vcomp A c⁻θ c⁺θ Bt Hθ κ₂) {x}
    (fv-vcomp-c A c⁻θ c⁺θ Bt Hθ κ₂ {x}
      (fv-wgo-σ Γ σ₀ w ρ {x} (∈-++r {x} (fvSub (wsub Γ a λ′ ,ₛ var w ,ₛ s ,ₛ t)) (x ∷ []) (∈-here x []))))
  where
  open EgTm Γ a λ′ w s t x ρ b Ps Pt hiding (eg)
  σ₀ = wsub Γ a λ′ ,ₛ var w ,ₛ s ,ₛ t ,ₛ var x

-- A 2-path term of length two contains both generators.
module _ (Γ : Ctx) (key : Nat → Nat) (p⁻ p⁺ : Nat → List Nat) where
  open Term Γ key p⁻ p⁺

  fv-egW : ∀ a b l α r {v w s t} → lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
           α ∈ fvTm (egW a b (wg l α r))
  fv-egW a b l α r {v} {w} {s} {t} lk rewrite lk = fv-eg Γ a l w s t α r b (p⁻ α) (p⁺ α)

  fv-term₂ : ∀ a b l α r l′ α′ r′ {v w s t v′ w′ s′ t′} →
             lookup Γ α ≡ just (arr (arr ⋆ (var v) (var w)) s t) →
             lookup Γ α′ ≡ just (arr (arr ⋆ (var v′) (var w′)) s′ t′) →
             (α ∈ fvTm (term a b (wg l α r ∷ wg l′ α′ r′ ∷ []))) × (α′ ∈ fvTm (term a b (wg l α r ∷ wg l′ α′ r′ ∷ [])))
  fv-term₂ a b l α r l′ α′ r′ lk lk′ =
    fv-vcomp-c A₀ Bs Bt Bu c h {α} (fv-egW a b l α r lk) ,
    fv-vcomp-h A₀ Bs Bt Bu c h {α′} (fv-egW a b l′ α′ r′ lk′)
    where
    A₀ = arr ⋆ (var a) (var b)
    Bs = B Γ a (l ++ p⁻ α ++ r)
    Bt = B Γ a (l ++ p⁺ α ++ r)
    Bu = B Γ a (l′ ++ p⁺ α′ ++ r′)
    c  = egW a b (wg l α r)
    h  = egW a b (wg l′ α′ r′)

------------------------------------------------------------------------
-- The two-disc context.

module TwoDisc (m k n : Nat) where
  -- The blocks: C₀ m, the first disc, the middle chain, the second
  -- disc, the last chain.
  C₁ : Ctx
  C₁ = C₀ m

  open Disc C₁ (e₀ m) public using () renaming (L to L₁; F to F₁; D to D₁; lk-f to lk-f₁; lk-f′ to lk-f₁′; lk-Z to lk-Z₁)

  C₂ : Ctx
  C₂ = chainFrom D₁ L₁ k            -- = colCtx m k

  open Disc C₂ (colEnd m k) public using () renaming (L to L₂; F to F₂; D to D₂; lk-f to lk-f₂; lk-f′ to lk-f₂′; lk-Z to lk-Z₂)

  E : Ctx
  E = chainFrom D₂ L₂ n

  b : Nat
  b = endFrom D₂ L₂ n

  f₁ f₁′ Z₁ f₂ f₂′ Z₂ : Nat
  f₁  = suc L₁
  f₁′ = suc (suc L₁)
  Z₁  = suc (suc (suc L₁))
  f₂  = suc L₂
  f₂′ = suc (suc L₂)
  Z₂  = suc (suc (suc L₂))

  λ′ μ ρ : List Nat
  λ′ = chEdges 1 m
  μ  = chEdges (len D₁) k
  ρ  = chEdges (len D₂) n

  S₀ T₀ : List Nat
  S₀ = λ′ ++ f₁  ∷ μ ++ f₂  ∷ ρ
  T₀ = λ′ ++ f₁′ ∷ μ ++ f₂′ ∷ ρ

  -- Extensions into E.
  x₅ : Ext D₂ E
  x₅ = ext-chain D₂ L₂ n
  x₄ : Ext C₂ E
  x₄ l = x₅ (ext-raised C₂ (colEnd m k) ⋆ l)
  x₃ : Ext D₁ E
  x₃ l = x₄ (ext-chain D₁ L₁ k l)
  x₂ : Ext C₁ E
  x₂ l = x₃ (ext-raised C₁ (e₀ m) ⋆ l)
  x₁ : Ext (ε ▸ ⋆) E
  x₁ l = x₂ (ext-chain (ε ▸ ⋆) 0 m l)

  ----------------------------------------------------------------------
  -- E is the context of a pasting tree.

  τ : Tree
  τ = node (leaves m ++ col ∷ leaves k ++ col ∷ leaves n)

  private
    build-++ : ∀ xs ys {Γ x A} (d : Γ ⊢ps x ∶ A) →
               buildList (xs ++ ys) d ≡ buildList ys (snd (snd (buildList xs d)))
    build-++ []       ys d = refl
    build-++ (t ∷ xs) ys d = build-++ xs ys (psd (snd (snd (build t (pse d)))))

    dm = snd (snd (buildList (leaves m) pss))
    bm = build-leaves m pss
    d₁ = psd (psd (pse (pse dm)))
    dk = snd (snd (buildList (leaves k) d₁))
    bk = build-leaves k d₁
    d₂ = psd (psd (pse (pse dk)))

    -- After the first disc and the middle chain.
    mid : (fst (buildList (leaves k) d₁) ≡ C₂) × (fst (snd (buildList (leaves k) d₁)) ≡ colEnd m k)
    mid = trans (fst bk) (cong₂ (λ Γ x → chainFrom (Raised Γ x ⋆) (len Γ) k) (fst bm) (snd bm)) ,
          trans (snd bk) (cong₂ (λ Γ x → endFrom (Raised Γ x ⋆) (len Γ) k) (fst bm) (snd bm))

  τ-ctx : ctxOf τ ≡ E
  τ-ctx =
    trans (cong fst (build-++ (leaves m) (col ∷ leaves k ++ col ∷ leaves n) pss))
      (trans (cong fst (build-++ (leaves k) (col ∷ leaves n) d₁))
        (trans (fst (build-leaves n d₂))
          (cong₂ (λ Γ x → chainFrom (Raised Γ x ⋆) (len Γ) n) (fst mid) (snd mid))))

  E-ps : E ⊢ps
  E-ps = ps (subst (λ Γ → Γ ⊢ps fst (snd (build τ pss)) ∶ ⋆) τ-ctx (snd (snd (build τ pss))))

  E-wf : E ⊢ctx
  E-wf with E-ps
  ... | ps d = fst (ps-wf d)

  d0 : E ⊢tm var 0 ∶ ⋆
  d0 = var-wf E-wf (x₁ refl)

  ----------------------------------------------------------------------
  -- The walks S₀ and T₀.

  private
    w₁ : Walk E 0 λ′ (e₀ m)
    w₁ = walk-ext x₂ (walk-chain (ε ▸ ⋆) 0 m)
    w₃ : Walk E L₁ μ (colEnd m k)
    w₃ = walk-ext x₄ (walk-chain D₁ L₁ k)
    w₅ : Walk E L₂ ρ b
    w₅ = walk-ext (λ l → l) (walk-chain D₂ L₂ n)

  walk-S : Walk E 0 S₀ b
  walk-S = walk-++ w₁ (cons (x₃ lk-f₁) (walk-++ w₃ (cons (x₅ lk-f₂) w₅)))

  walk-T : Walk E 0 T₀ b
  walk-T = walk-++ w₁ (cons (x₃ lk-f₁′) (walk-++ w₃ (cons (x₅ lk-f₂′) w₅)))

  ----------------------------------------------------------------------
  -- The two orders.

  KE : Key2Ctx E
  KE = key2-ps E-ps

  open Key2Ctx KE using (key; p⁻; p⁺)
  open Term E key p⁻ p⁺

  lkZ₁ : lookup E Z₁ ≡ just (arr F₁ (var f₁) (var f₁′))
  lkZ₁ = x₃ lk-Z₁

  lkZ₂ : lookup E Z₂ ≡ just (arr F₂ (var f₂) (var f₂′))
  lkZ₂ = x₅ lk-Z₂

  private
    s₁ : p⁻ Z₁ ≡ f₁ ∷ []
    s₁ = srcVar-eq lkZ₁
    t₁ : p⁺ Z₁ ≡ f₁′ ∷ []
    t₁ = tgtVar-eq lkZ₁
    s₂ : p⁻ Z₂ ≡ f₂ ∷ []
    s₂ = srcVar-eq lkZ₂
    t₂ : p⁺ Z₂ ≡ f₂′ ∷ []
    t₂ = tgtVar-eq lkZ₂

    G₁ : Var2 E Z₁
    G₁ = (e₀ m , L₁ , var f₁ , var f₁′ , lkZ₁)
    G₂ : Var2 E Z₂
    G₂ = (colEnd m k , L₂ , var f₂ , var f₂′ , lkZ₂)

    -- (λ ++ a ∷ μ) ++ X ++ ρ  ≡  λ ++ a ∷ μ ++ X ++ ρ
    re : ∀ a X → (λ′ ++ a ∷ μ) ++ X ++ ρ ≡ λ′ ++ a ∷ μ ++ X ++ ρ
    re a X = ++-assoc λ′ (a ∷ μ) (X ++ ρ)

  P Q : List WG
  P = wg λ′ Z₁ (μ ++ f₂ ∷ ρ) ∷ wg (λ′ ++ f₁′ ∷ μ) Z₂ ρ ∷ []
  Q = wg (λ′ ++ f₁ ∷ μ) Z₂ ρ ∷ wg λ′ Z₁ (μ ++ f₂′ ∷ ρ) ∷ []

  chain-P : Chain S₀ P T₀
  chain-P =
    cons G₁ (cong (λ X → λ′ ++ X ++ μ ++ f₂ ∷ ρ) s₁)
      (subst (λ T′ → Chain (λ′ ++ p⁺ Z₁ ++ μ ++ f₂ ∷ ρ) (wg (λ′ ++ f₁′ ∷ μ) Z₂ ρ ∷ []) T′)
             (trans (re f₁′ (p⁺ Z₂)) (cong (λ X → λ′ ++ f₁′ ∷ μ ++ X ++ ρ) t₂))
        (cons G₂ (trans (re f₁′ (p⁻ Z₂))
                        (trans (cong (λ X → λ′ ++ f₁′ ∷ μ ++ X ++ ρ) s₂)
                               (cong (λ X → λ′ ++ X ++ μ ++ f₂ ∷ ρ) (sym t₁))))
                 nil))

  chain-Q : Chain S₀ Q T₀
  chain-Q =
    cons G₂ (trans (re f₁ (p⁻ Z₂)) (cong (λ X → λ′ ++ f₁ ∷ μ ++ X ++ ρ) s₂))
      (subst (λ T′ → Chain ((λ′ ++ f₁ ∷ μ) ++ p⁺ Z₂ ++ ρ) (wg λ′ Z₁ (μ ++ f₂′ ∷ ρ) ∷ []) T′)
             (cong (λ X → λ′ ++ X ++ μ ++ f₂′ ∷ ρ) t₁)
        (cons G₁ (trans (cong (λ X → λ′ ++ X ++ μ ++ f₂′ ∷ ρ) s₁)
                        (sym (trans (re f₁ (p⁺ Z₂)) (cong (λ X → λ′ ++ f₁ ∷ μ ++ X ++ ρ) t₂))))
                 nil))

  A₀ : Ty
  A₀ = arr ⋆ (var 0) (var b)

  Lt Rt : Tm
  Lt = term 0 b P
  Rt = term 0 b Q

  ok : BdOK
  ok = key2-bdok E-wf KE

  L-wf : E ⊢tm Lt ∶ arr A₀ (B E 0 S₀) (B E 0 T₀)
  L-wf = term-wf ok d0 chain-P walk-S

  R-wf : E ⊢tm Rt ∶ arr A₀ (B E 0 S₀) (B E 0 T₀)
  R-wf = term-wf ok d0 chain-Q walk-S

  ----------------------------------------------------------------------
  -- Fullness.

  AE : Ty
  AE = arr A₀ (B E 0 S₀) (B E 0 T₀)

  private
    sc-fvTy : ∀ N A {j} → S.ScTy N A → j ∈ fvTy A → j < N
    sc-fvTy N ⋆ _ ()
    sc-fvTy N (arr A t u) (hA , ht , hu) q with ∈-++ (fvTy A) (fvTm t ++ fvTm u) q
    ... | inj₁ r = sc-fvTy N A hA r
    ... | inj₂ r with ∈-++ (fvTm t) (fvTm u) r
    ...   | inj₁ s = sc-fv N t ht s
    ...   | inj₂ s = sc-fv N u hu s

  full-from : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Cov Γ (fvTmTy t A) → T (≈? (fvTmTy t A) (varsCtx Γ))
  full-from {Γ} {t} {A} dt c =
    ∧-intro (all-intro (λ x → elem x (varsCtx Γ)) (fvTmTy t A) (λ j q → elem-downFrom (bound j q)))
            (all-intro (λ x → elem x (fvTmTy t A)) (varsCtx Γ) (λ j q → c (downFrom-mem (len Γ) q)))
    where
    bound : ∀ j → j ∈ fvTmTy t A → j < len Γ
    bound j q with ∈-++ (fvTm t) (fvTy A) q
    ... | inj₁ r = sc-fv (len Γ) t (S.tm-sc closed dt) r
    ... | inj₂ r = sc-fvTy (len Γ) A (S.tm-ty-sc closed dt) r

  -- Every variable of E is in t : AE, if Z₁ and Z₂ are in t.
  module _ (t : Tm) (hZ₁ : Z₁ ∈ fvTm t) (hZ₂ : Z₂ ∈ fvTm t) where
    private
      X = fvTmTy t AE

      inS : ∀ {j} → j ∈ fvTm (B E 0 S₀) → j ∈ X
      inS {j} q = ∈-++r {j} (fvTm t) (fvTy AE) (∈-++r {j} (fvTy A₀) (fvTm (B E 0 S₀) ++ fvTm (B E 0 T₀))
                    (∈-++l {j} (fvTm (B E 0 S₀)) (fvTm (B E 0 T₀)) q))

      inT : ∀ {j} → j ∈ fvTm (B E 0 T₀) → j ∈ X
      inT {j} q = ∈-++r {j} (fvTm t) (fvTy AE) (∈-++r {j} (fvTy A₀) (fvTm (B E 0 S₀) ++ fvTm (B E 0 T₀))
                    (∈-++r {j} (fvTm (B E 0 S₀)) (fvTm (B E 0 T₀)) q))

      -- An edge of S₀ with a known target.
      edgeS : ∀ e {u v} → e ∈ S₀ → lookup E e ≡ just (arr ⋆ (var u) (var v)) → (e ∈ X) × (v ∈ X)
      edgeS e {u} {v} q l =
        inS (fst h) , subst (_∈ X) (tgtOf-eq {E} l) (inS (snd h))
        where h = fv-wgo E (⟨⟩ ,ₛ var 0) 0 S₀ e q

      chainS : ∀ Γ x j {e} → Ext (chainFrom Γ x j) E → (∀ {e} → e ∈ chEdges (len Γ) j → e ∈ S₀) →
               e ∈ chEdges (len Γ) j → (e ∈ X) × (pred e ∈ X)
      chainS Γ x j {e} xe sub q with lk-chain Γ x j e q
      ... | u , l = edgeS e (sub q) (xe l)

      rest : List Nat
      rest = μ ++ f₂ ∷ ρ

      inλ : ∀ {e} → e ∈ λ′ → e ∈ S₀
      inλ {e} q = ∈-++l {e} λ′ (f₁ ∷ rest) q
      inμ : ∀ {e} → e ∈ μ → e ∈ S₀
      inμ {e} q = ∈-++r {e} λ′ (f₁ ∷ rest) (∈-there {e} f₁ rest (∈-++l {e} μ (f₂ ∷ ρ) q))
      inρ : ∀ {e} → e ∈ ρ → e ∈ S₀
      inρ {e} q = ∈-++r {e} λ′ (f₁ ∷ rest) (∈-there {e} f₁ rest (∈-++r {e} μ (f₂ ∷ ρ) (∈-there {e} f₂ ρ q)))
      f₁∈ : f₁ ∈ S₀
      f₁∈ = ∈-++r {f₁} λ′ (f₁ ∷ rest) (∈-here f₁ rest)
      f₂∈ : f₂ ∈ S₀
      f₂∈ = ∈-++r {f₂} λ′ (f₁ ∷ rest) (∈-there {f₂} f₁ rest (∈-++r {f₂} μ (f₂ ∷ ρ) (∈-here f₂ ρ)))

      rest′ : List Nat
      rest′ = μ ++ f₂′ ∷ ρ

      f₁′∈ : f₁′ ∈ fvTm (B E 0 T₀)
      f₁′∈ = fst (fv-wgo E (⟨⟩ ,ₛ var 0) 0 T₀ f₁′ (∈-++r {f₁′} λ′ (f₁′ ∷ rest′) (∈-here f₁′ rest′)))
      f₂′∈ : f₂′ ∈ fvTm (B E 0 T₀)
      f₂′∈ = fst (fv-wgo E (⟨⟩ ,ₛ var 0) 0 T₀ f₂′
                (∈-++r {f₂′} λ′ (f₁′ ∷ rest′) (∈-there {f₂′} f₁′ rest′ (∈-++r {f₂′} μ (f₂′ ∷ ρ) (∈-here f₂′ ρ)))))

      cov₀ : Cov (ε ▸ ⋆) X
      cov₀ (s≤s z≤n) = ∈-++r {0} (fvTm t) (fvTy AE) (∈-here 0 (b ∷ [] ++ fvTm (B E 0 S₀) ++ fvTm (B E 0 T₀)))

    cover : Cov E X
    cover =
      cov-chain D₂ L₂ n X
        (cov-raised C₂ (colEnd m k) X
          (cov-chain D₁ L₁ k X
            (cov-raised C₁ (e₀ m) X
              (cov-chain (ε ▸ ⋆) 0 m X cov₀ (λ e q → chainS (ε ▸ ⋆) 0 m x₂ inλ q))
              (snd (edgeS f₁ f₁∈ (x₃ lk-f₁))) (fst (edgeS f₁ f₁∈ (x₃ lk-f₁))) (inT f₁′∈) (∈-++l {Z₁} (fvTm t) (fvTy AE) hZ₁))
            (λ e q → chainS D₁ L₁ k x₄ inμ q))
          (snd (edgeS f₂ f₂∈ (x₅ lk-f₂))) (fst (edgeS f₂ f₂∈ (x₅ lk-f₂))) (inT f₂′∈) (∈-++l {Z₂} (fvTm t) (fvTy AE) hZ₂))
        (λ e q → chainS D₂ L₂ n (λ l → l) inρ q)

  full-L : T (≈? (fvTmTy Lt AE) (varsCtx E))
  full-L = full-from L-wf (cover Lt (fst fvL) (snd fvL))
    where fvL = fv-term₂ E key p⁻ p⁺ 0 b λ′ Z₁ (μ ++ f₂ ∷ ρ) (λ′ ++ f₁′ ∷ μ) Z₂ ρ lkZ₁ lkZ₂

  full-R : T (≈? (fvTmTy Rt AE) (varsCtx E))
  full-R = full-from R-wf (cover Rt (snd fvR) (fst fvR))
    where fvR = fv-term₂ E key p⁻ p⁺ 0 b (λ′ ++ f₁ ∷ μ) Z₂ ρ λ′ Z₁ (μ ++ f₂′ ∷ ρ) lkZ₂ lkZ₁

  ----------------------------------------------------------------------
  -- The exchange cells.

  xch-wf : ∀ {Γ θ} → Γ ⊢sub θ ∶ E → Γ ⊢tm coh E (arr AE Lt Rt) θ ∶ arr AE Lt Rt [ θ ]ty
  xch-wf sθ =
    coh-wf E-ps E-wf (arr-wf L-wf R-wf) (∨-inl′ (∧-intro full-L full-R)) sθ
    where
    ∨-inl′ : ∀ {a b} → T a → T (a ∨ b)
    ∨-inl′ {true} _ = tt

  xch-wf′ : ∀ {Γ θ} → Γ ⊢sub θ ∶ E → Γ ⊢tm coh E (arr AE Rt Lt) θ ∶ arr AE Rt Lt [ θ ]ty
  xch-wf′ sθ =
    coh-wf E-ps E-wf (arr-wf R-wf L-wf) (∨-inl′ (∧-intro full-R full-L)) sθ
    where
    ∨-inl′ : ∀ {a b} → T a → T (a ∨ b)
    ∨-inl′ {true} _ = tt
