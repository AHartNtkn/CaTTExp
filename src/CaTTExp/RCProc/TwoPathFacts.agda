------------------------------------------------------------------------
-- Two facts about the Theorem A hypothesis `Key2Ctx`
-- (CaTTExp.RCProc.TwoPathCtx), ledger S20 (i), stage 3f.
--
--  * `key2-ps`: every pasting context satisfies Key2Ctx. The key is the
--    position in the creation order `olist` of CaTTExp.Strict.Order,
--    whose invariant `OInv` (`oinv-⊢ps`) puts the endpoints of every
--    arrow before and after it. The boundary paths of a 2-variable are
--    its source and target variables.
--
--  * Some such condition is needed. In Γ = (x, y, f : x → y, g h : f ⇒ f)
--    the 2-paths g;h and h;g start at the same 1-path f and use the same
--    2-variables, but they are not exchange-equivalent (`gh-not-~`),
--    so the conclusion of TwoPath's `exchange-complete` fails without
--    Key2; and Key2Ctx Γ has no instance (`no-key2`).
--    That g ∗₁ h and h ∗₁ g are not connected by any CaTT 3-cell is
--    proved by a model argument in CaTTExp.RCProc.TwoPathModel
--    (`no-3cell`).
------------------------------------------------------------------------
module CaTTExp.RCProc.TwoPathFacts where

open import CaTTExp.Prelude
open import CaTTExp.Pure

open import CaTTExp.PastingCheck ∅ using (PsTy; ⋆ₚ; arrₚ)
open import CaTTExp.Strict.PsFacts ∅ using (ps-facts; ord; shape; lookup-<)
open import CaTTExp.Strict.Order using (olist; pos; OInv; faces; oinv-⊢ps)
open import CaTTExp.Strict.Bag using (_≈_; ≡→≈; ≈-refl; ≈-sym; ≈-trans)
open import CaTTExp.Strict.Cell using (top)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (⟦_⟧; η; η-top)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; <-irrefl)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.RCProc.TwoPath
open import CaTTExp.RCProc.TwoPathCtx

private
  T< : ∀ a b → T (a <ℕ b) → a < b
  T< zero    zero    ()
  T< zero    (suc b) _ = s≤s z≤n
  T< (suc a) zero    ()
  T< (suc a) (suc b) p = s≤s (T< a b p)

  <-tr : ∀ {a b c} → a < b → b < c → a < c
  <-tr {a} {b} {c} p q = <-trans p q

------------------------------------------------------------------------
-- Pasting contexts.

-- The source and target variables of a 2-variable.
srcVar tgtVar : Maybe Ty → List Nat
srcVar (just (arr _ (var s) _)) = s ∷ []
srcVar _                        = []
tgtVar (just (arr _ _ (var t))) = t ∷ []
tgtVar _                        = []

srcVar-eq : ∀ {m A s t} → m ≡ just (arr A (var s) t) → srcVar m ≡ s ∷ []
srcVar-eq refl = refl

tgtVar-eq : ∀ {m A s t} → m ≡ just (arr A s (var t)) → tgtVar m ≡ t ∷ []
tgtVar-eq refl = refl

key2-ps : ∀ {Γ} → Γ ⊢ps → Key2Ctx Γ
key2-ps {Γ} (ps {x = z} d) = record
  { key = P ; p⁻ = λ α → srcVar (lookup Γ α) ; p⁺ = λ α → tgtVar (lookup Γ α)
  ; order = record { k₁ = k₁ ; bd = bd ; k⁻ = k⁻ ; k⁺ = k⁺ }
  ; img⁻ = img⁻ ; img⁺ = img⁺ }
  where
  I : OInv Γ
  I = oinv-⊢ps (ps d)
  F = ps-facts d
  P : Nat → Nat
  P v = pos v (olist Γ)
  C2 = ctxComp2 Γ P (λ α → srcVar (lookup Γ α)) (λ α → tgtVar (lookup Γ α))
  open TwoPaths C2 using (Path1; nil; cons)

  k₁ : ∀ e → Var1 Γ e → (P (src₀ Γ e) < P e) × (P e < P (tgt₀ Γ e))
  k₁ e (x , y , eq) with faces I e ⋆ x y eq
  ... | _ , _ , ls , lt rewrite src₀-ok Γ e eq | tgt₀-ok Γ e eq = T< _ _ ls , T< _ _ lt

  -- A 2-variable's boundaries are variables, of the base arrow type.
  shape2 : ∀ α {a b s t} → lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t) →
           Σ Nat λ s′ → Σ Nat λ t′ → (s ≡ var s′) × (t ≡ var t′)
  shape2 α eq with shape F α _ eq
  ... | arrₚ {x = s′} {y = t′} _ = s′ , t′ , refl , refl

  bd : ∀ α → Var2 Γ α → Σ Nat λ a → Σ Nat λ b →
       Path1 a (srcVar (lookup Γ α)) b × Path1 a (tgtVar (lookup Γ α)) b × (P a < P b)
  bd α (a , b , s , t , eq) with shape2 α eq
  ... | s′ , t′ , refl , refl with ord F α _ s′ t′ eq
  ...   | ls , lt , _ =
    a , b , subst (λ L → Path1 a L b) (sym (srcVar-eq eq)) (path s′ ls) ,
            subst (λ L → Path1 a L b) (sym (tgtVar-eq eq)) (path t′ lt) ,
            subst (λ w → P a < P w) (tgt₀-ok Γ s′ ls)
              (subst (λ w → P w < P (tgt₀ Γ s′)) (src₀-ok Γ s′ ls) (<-tr (fst (k₁ s′ e₁)) (snd (k₁ s′ e₁))))
    where
    e₁ : Var1 Γ s′
    e₁ = a , b , ls
    path : ∀ v → lookup Γ v ≡ just (arr ⋆ (var a) (var b)) → Path1 a (v ∷ []) b
    path v l = cons (a , b , l) (src₀-ok Γ v l)
                 (subst (λ w → Path1 w [] b) (sym (tgt₀-ok Γ v l)) nil)

  k⁻ : ∀ α e → Var2 Γ α → e ∈ srcVar (lookup Γ α) → P e < P α
  k⁻ α e (a , b , s , t , eq) i with shape2 α eq
  ... | s′ , t′ , refl , refl with faces I α (arr ⋆ (var a) (var b)) s′ t′ eq
  ...   | _ , _ , ls , _ with subst (e ∈_) (srcVar-eq eq) i
  ...     | here = T< _ _ ls
  ...     | there ()

  k⁺ : ∀ α e → Var2 Γ α → e ∈ tgtVar (lookup Γ α) → P α < P e
  k⁺ α e (a , b , s , t , eq) i with shape2 α eq
  ... | s′ , t′ , refl , refl with faces I α (arr ⋆ (var a) (var b)) s′ t′ eq
  ...   | _ , _ , _ , lt with subst (e ∈_) (tgtVar-eq eq) i
  ...     | here = T< _ _ lt
  ...     | there ()

  varTop : ∀ v {A} → lookup Γ v ≡ just A → top (⟦ var v ⟧ (η Γ)) ≈ tups (v ∷ [])
  varTop v l = ≡→≈ (trans (η-top Γ v) (if-T (v <ℕ len Γ) (lookup-< Γ v l)))
    where
    if-T : ∀ b {X Y : List (List Nat)} → T b → (if b then X else Y) ≡ X
    if-T true _ = refl

  img⁻ : ∀ α {a b s t} → lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t) →
         top (⟦ s ⟧ (η Γ)) ≈ tups (srcVar (lookup Γ α))
  img⁻ α eq with shape2 α eq
  ... | s′ , t′ , refl , refl with ord F α _ s′ t′ eq
  ...   | ls , _ , _ = subst (λ L → top (⟦ var s′ ⟧ (η Γ)) ≈ tups L) (sym (srcVar-eq eq)) (varTop s′ ls)

  img⁺ : ∀ α {a b s t} → lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t) →
         top (⟦ t ⟧ (η Γ)) ≈ tups (tgtVar (lookup Γ α))
  img⁺ α eq with shape2 α eq
  ... | s′ , t′ , refl , refl with ord F α _ s′ t′ eq
  ...   | _ , lt , _ = subst (λ L → top (⟦ var t′ ⟧ (η Γ)) ≈ tups L) (sym (tgtVar-eq eq)) (varTop t′ lt)

------------------------------------------------------------------------
-- The counterexample without Key2: x, y, f : x → y, g h : f ⇒ f
-- (levels 0, 1, 2, 3, 4).

Γgh : Ctx
Γgh = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1)
        ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 2)
        ▸ arr (arr ⋆ (var 0) (var 1)) (var 2) (var 2)

module Counterexample (key : Nat → Nat) where
  Cgh : Comp2
  Cgh = ctxComp2 Γgh key (λ _ → 2 ∷ []) (λ _ → 2 ∷ [])
  open TwoPaths Cgh

  P Q : List WG
  P = wg [] 3 [] ∷ wg [] 4 [] ∷ []
  Q = wg [] 4 [] ∷ wg [] 3 [] ∷ []

  G3 : Var2 Γgh 3
  G3 = 0 , 1 , var 2 , var 2 , refl
  G4 : Var2 Γgh 4
  G4 = 0 , 1 , var 2 , var 2 , refl

  f-path : Path1 0 (2 ∷ []) 1
  f-path = cons (0 , 1 , refl) refl nil

  chainP : Chain (2 ∷ []) P (2 ∷ [])
  chainP = cons G3 refl (cons G4 refl nil)
  chainQ : Chain (2 ∷ []) Q (2 ∷ [])
  chainQ = cons G4 refl (cons G3 refl nil)

  bagPQ : bagG P ≋ bagG Q
  bagPQ = ≋-swap 3 4 []

  -- Lists of unwhiskered generators admit no exchange, in either
  -- direction: every exchange whiskers by a nonempty 1-path.
  Bare : List WG → Set
  Bare []               = ⊤
  Bare (wg l _ r ∷ R)   = (l ≡ []) × (r ≡ []) × Bare R

  private
    ++-ne : ∀ (m c : List Nat) → (m ++ 2 ∷ c) ≡ [] → ⊥
    ++-ne []      c ()
    ++-ne (_ ∷ m) c ()

  bare-out : ∀ {R S} → Xch R S → Bare R → ⊥
  bare-out (xch a α m β c) (_ , r≡ , _) = ++-ne m c r≡
  bare-out (skip w x)      (_ , _ , b)  = bare-out x b

  bare-in : ∀ {R S} → Xch S R → Bare R → ⊥
  bare-in (xch a α m β c) (l≡ , _) = ++-ne a m l≡
  bare-in (skip w x)      (_ , _ , b) = bare-in x b

  bare-~ : ∀ {R S} → R ~ S → Bare R → R ≡ S
  bare-~ done      _ = refl
  bare-~ (fwd x _) b = ⊥-elim (bare-out x b)
  bare-~ (bwd x _) b = ⊥-elim (bare-in x b)

  -- g;h and h;g: same source path, same 2-variables, not
  -- exchange-equivalent.
  gh-not-~ : P ~ Q → ⊥
  gh-not-~ e with bare-~ e (refl , refl , refl , refl , tt)
  ... | ()

-- No key makes Γgh strongly ordered.
no-key2 : Key2Ctx Γgh → ⊥
no-key2 K = <-irrefl (<-trans k23 k32)
  where
  open Key2Ctx K
  open TwoPaths (ctxComp2 Γgh key p⁻ p⁺) using (module Key2)
  open Key2 order using (k⁻; k⁺)
  G3 : Var2 Γgh 3
  G3 = 0 , 1 , var 2 , var 2 , refl
  in⁻ : 2 ∈ p⁻ 3
  in⁻ = ≋-∈ (tups-≋ (2 ∷ []) (p⁻ 3) (img⁻ 3 refl)) here
  in⁺ : 2 ∈ p⁺ 3
  in⁺ = ≋-∈ (tups-≋ (2 ∷ []) (p⁺ 3) (img⁺ 3 refl)) here
  k23 : key 2 < key 3
  k23 = k⁻ 3 2 G3 in⁻
  k32 : key 3 < key 2
  k32 = k⁺ 3 2 G3 in⁺
