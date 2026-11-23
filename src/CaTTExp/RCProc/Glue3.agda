------------------------------------------------------------------------
-- 3-cell glue for 2-cells between 1-cells (ledger S20 (i), stage 3e;
-- notes/relative-coherence.md §2 Step 3).
--
-- For 2-cells over A = x → y, vertical composition is
-- vcomp A t s u c h : t ⇒ u (RCProc.Eg). Each lemma here is one fixed
-- coherence over a small pasting context Θ, pulled back along the
-- substitution of its arguments:
--
--   congL : c ⇛ c′  ⟹  c ∗ h ⇛ c′ ∗ h          (Θc)
--   congR : h ⇛ h′  ⟹  c ∗ h ⇛ c ∗ h′          (Θh)
--   assoc : (c ∗ h) ∗ k ⇛ c ∗ (h ∗ k), and back  (Θa)
--
-- The shape data of each coherence (Θ ⊢ps, Θ ⊢ctx, the type and the
-- side condition) is taken from the typing derivation that the checker
-- `infer` returns for it on the identity substitution; Agda evaluates
-- `infer` on these closed inputs when it type-checks this module, and
-- `from-just` needs that evaluation to succeed. `retarget` reuses the
-- data at any typed substitution. The type of the pulled-back cell is
-- the expected one by computation.
--
-- Also here (second half of the file): `cancel`, any two parallel
-- 2-cells over x → y whose free variables are all of dimension ≤ 1
-- are connected, by RCProc.rcS on their support (Lemma P,
-- `rcS-graphSupp`). Chain fillers and composites of them satisfy this
-- (`low-coh`, `low-vcomp`), so adjacent fillers cancel.
------------------------------------------------------------------------
module CaTTExp.RCProc.Glue3 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (idS; tm-ty; tm-ctx)
open import CaTTExp.RCProc.Eg using (vcomp)
open import CaTTExp.RCProc.Glue using (Ans)

-- Reuse the shape data of a coherence derivation at another substitution.
retarget : ∀ {Δ Γ Θ A t u σ₀ X σ} → Δ ⊢tm coh Θ (arr A t u) σ₀ ∶ X → Γ ⊢sub σ ∶ Θ →
           Γ ⊢tm coh Θ (arr A t u) σ ∶ arr A t u [ σ ]ty
retarget (coh-wf p w ty sd _) s = coh-wf p w ty sd s

private
  A′ : Ty
  A′ = arr ⋆ (var 0) (var 1)

  -- The boundary of a 2-cell over x → y.
  bd2 : ∀ {Γ x y t s c} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s →
        (Γ ⊢tm x ∶ ⋆) × (Γ ⊢tm y ∶ ⋆) × (Γ ⊢tm t ∶ arr ⋆ x y) × (Γ ⊢tm s ∶ arr ⋆ x y)
  bd2 dc with tm-ty dc
  ... | arr-wf dt ds with tm-ty dt
  ...   | arr-wf dx dy = dx , dy , dt , ds

  bd3 : ∀ {Γ B c c′ w} → Γ ⊢tm w ∶ arr B c c′ → (Γ ⊢tm c ∶ B) × (Γ ⊢tm c′ ∶ B)
  bd3 dw with tm-ty dw
  ... | arr-wf dc dc′ = dc , dc′

  s₂ : ∀ {Γ x y} → Γ ⊢tm x ∶ ⋆ → Γ ⊢tm y ∶ ⋆ → Γ ⊢sub (⟨⟩ ,ₛ x ,ₛ y) ∶ (ε ▸ ⋆ ▸ ⋆)
  s₂ dx dy = ,-wf (,-wf (⟨⟩-wf (tm-ctx dx)) dx) dy

------------------------------------------------------------------------
-- Congruence in the left slot.

-- a, b, t, s, c, c′, w : c ⇛ c′, u, h : s ⇒ u.
Θc : Ctx
Θc = ε ▸ ⋆ ▸ ⋆ ▸ A′ ▸ A′ ▸ arr A′ (var 2) (var 3) ▸ arr A′ (var 2) (var 3)
       ▸ arr (arr A′ (var 2) (var 3)) (var 4) (var 5) ▸ A′ ▸ arr A′ (var 3) (var 7)

Tc : Ty
Tc = arr (arr A′ (var 2) (var 7)) (vcomp A′ (var 2) (var 3) (var 7) (var 4) (var 8))
                                   (vcomp A′ (var 2) (var 3) (var 7) (var 5) (var 8))

private
  dTc = snd (from-just (infer Θc (coh Θc Tc (idS 9))))

congL : ∀ {Γ x y t s u c c′ h} → Γ ⊢tm h ∶ arr (arr ⋆ x y) s u →
        Ans Γ (arr (arr ⋆ x y) t s) c c′ →
        Ans Γ (arr (arr ⋆ x y) t u) (vcomp (arr ⋆ x y) t s u c h) (vcomp (arr ⋆ x y) t s u c′ h)
congL {Γ} {x} {y} {t} {s} {u} {c} {c′} {h} dh (w , dw) =
  coh Θc Tc σ , retarget dTc sσ
  where
  σ = ⟨⟩ ,ₛ x ,ₛ y ,ₛ t ,ₛ s ,ₛ c ,ₛ c′ ,ₛ w ,ₛ u ,ₛ h
  dcc = bd3 dw
  b = bd2 (fst dcc)
  du = snd (snd (snd (bd2 dh)))
  sσ : Γ ⊢sub σ ∶ Θc
  sσ = ,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (s₂ (fst b) (fst (snd b)))
         (fst (snd (snd b)))) (snd (snd (snd b)))) (fst dcc)) (snd dcc)) dw) du) dh

------------------------------------------------------------------------
-- Congruence in the right slot.

-- a, b, t, s, c : t ⇒ s, u, h, h′, w : h ⇛ h′.
Θh : Ctx
Θh = ε ▸ ⋆ ▸ ⋆ ▸ A′ ▸ A′ ▸ arr A′ (var 2) (var 3) ▸ A′ ▸ arr A′ (var 3) (var 5)
       ▸ arr A′ (var 3) (var 5) ▸ arr (arr A′ (var 3) (var 5)) (var 6) (var 7)

Th : Ty
Th = arr (arr A′ (var 2) (var 5)) (vcomp A′ (var 2) (var 3) (var 5) (var 4) (var 6))
                                   (vcomp A′ (var 2) (var 3) (var 5) (var 4) (var 7))

private
  dTh = snd (from-just (infer Θh (coh Θh Th (idS 9))))

congR : ∀ {Γ x y t s u c h h′} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s →
        Ans Γ (arr (arr ⋆ x y) s u) h h′ →
        Ans Γ (arr (arr ⋆ x y) t u) (vcomp (arr ⋆ x y) t s u c h) (vcomp (arr ⋆ x y) t s u c h′)
congR {Γ} {x} {y} {t} {s} {u} {c} {h} {h′} dc (w , dw) =
  coh Θh Th σ , retarget dTh sσ
  where
  σ = ⟨⟩ ,ₛ x ,ₛ y ,ₛ t ,ₛ s ,ₛ c ,ₛ u ,ₛ h ,ₛ h′ ,ₛ w
  dhh = bd3 dw
  b = bd2 dc
  du = snd (snd (snd (bd2 (fst dhh))))
  sσ : Γ ⊢sub σ ∶ Θh
  sσ = ,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (s₂ (fst b) (fst (snd b)))
         (fst (snd (snd b)))) (snd (snd (snd b)))) dc) du) (fst dhh)) (snd dhh)) dw

------------------------------------------------------------------------
-- Associativity.

-- a, b, t, s, c : t ⇒ s, u, h : s ⇒ u, v, k : u ⇒ v.
Θa : Ctx
Θa = ε ▸ ⋆ ▸ ⋆ ▸ A′ ▸ A′ ▸ arr A′ (var 2) (var 3) ▸ A′ ▸ arr A′ (var 3) (var 5)
       ▸ A′ ▸ arr A′ (var 5) (var 7)

private
  La Ra : Tm
  La = vcomp A′ (var 2) (var 5) (var 7) (vcomp A′ (var 2) (var 3) (var 5) (var 4) (var 6)) (var 8)
  Ra = vcomp A′ (var 2) (var 3) (var 7) (var 4) (vcomp A′ (var 3) (var 5) (var 7) (var 6) (var 8))

Ta Ta′ : Ty
Ta  = arr (arr A′ (var 2) (var 7)) La Ra
Ta′ = arr (arr A′ (var 2) (var 7)) Ra La

private
  dTa  = snd (from-just (infer Θa (coh Θa Ta (idS 9))))
  dTa′ = snd (from-just (infer Θa (coh Θa Ta′ (idS 9))))

module _ {Γ x y t s u v c h k} (dc : Γ ⊢tm c ∶ arr (arr ⋆ x y) t s) (dh : Γ ⊢tm h ∶ arr (arr ⋆ x y) s u)
         (dk : Γ ⊢tm k ∶ arr (arr ⋆ x y) u v) where
  private
    A = arr ⋆ x y
    σ = ⟨⟩ ,ₛ x ,ₛ y ,ₛ t ,ₛ s ,ₛ c ,ₛ u ,ₛ h ,ₛ v ,ₛ k
    b = bd2 dc
    du = snd (snd (snd (bd2 dh)))
    dv = snd (snd (snd (bd2 dk)))
    sσ : Γ ⊢sub σ ∶ Θa
    sσ = ,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (,-wf (s₂ (fst b) (fst (snd b)))
           (fst (snd (snd b)))) (snd (snd (snd b)))) dc) du) dh) dv) dk

  assoc : Ans Γ (arr A t v) (vcomp A t u v (vcomp A t s u c h) k) (vcomp A t s v c (vcomp A s u v h k))
  assoc = coh Θa Ta σ , retarget dTa sσ

  assoc′ : Ans Γ (arr A t v) (vcomp A t s v c (vcomp A s u v h k)) (vcomp A t u v (vcomp A t s u c h) k)
  assoc′ = coh Θa Ta′ σ , retarget dTa′ sσ

------------------------------------------------------------------------
-- Cells built from 1-cells: any two parallel ones are connected.
--
-- A variable is low when its type is not of dimension ≥ 2. A term is
-- low when all its free variables are. Every 1-cell term is low
-- (`low1`: a 1-cell coherence is a composite over a chain, whose
-- arguments are 0- and 1-cells), and so is every coherence over a
-- graph context, such as a chain filler (`low-coh`), and every
-- vertical composite of low 2-cells (`low-vcomp`). The support of a
-- query between two low 2-cells is then a graph context
-- (`graph-supp`), so RCProc.rcS answers it (`rcS-graphSupp`, Lemma P):
--
--   cancel : u, v : p ⇒ q low  ⟹  Ans u v.

open import CaTTExp.GraphFillerTotal using (⋆-var; coh-view; CohV; cohV)
open import CaTTExp.GraphFillerTotal.Chains
  using (chainC; _⊎_; inj₁; inj₂; _∈_; ∈-here; ∈-there; ∈-++l; ∈-++r; ∈-++; ∈-single; ∨-elim)
open import CaTTExp.GraphFillerTotal.Higher using (Graph; isGraph; isGraph-ok)
open import CaTTExp.Weakening ∅ cattSide using (lookup-top; lookup-wk)
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as Sb
import CaTTExp.RCProc as RC

record Low (Γ : Ctx) (i : Nat) : Set where
  constructor mkLow
  field unLow : ∀ {A s t u v} → lookup Γ i ≡ just (arr (arr A s t) u v) → ⊥
open Low

LowL : Ctx → List Nat → Set
LowL Γ xs = ∀ {i} → i ∈ xs → Low Γ i

LowT : Ctx → Tm → Set
LowT Γ t = LowL Γ (fvTm t)

private
  just-inj : ∀ {A B : Ty} → just A ≡ just B → A ≡ B
  just-inj refl = refl

  low-++ : ∀ {Γ} xs ys → LowL Γ xs → LowL Γ ys → LowL Γ (xs ++ ys)
  low-++ xs ys h k {i} q with ∈-++ {i} xs ys q
  ... | inj₁ r = h r
  ... | inj₂ r = k r

  low-[] : ∀ {Γ} → LowL Γ []
  low-[] ()

  -- The two shapes of a type that is not of dimension ≥ 2.
  data Small : Ty → Set where
    s⋆ : Small ⋆
    s1 : ∀ a b → Small (arr ⋆ a b)

  small : ∀ {Γ} i A → lookup Γ i ≡ just A → (∀ {B s t u v} → lookup Γ i ≡ just (arr (arr B s t) u v) → ⊥) → Small A
  small i ⋆               _ _ = s⋆
  small i (arr ⋆ a b)     _ _ = s1 a b
  small i (arr (arr _ _ _) _ _) e l = ⊥-elim (l e)

graph-chain : ∀ k → Graph (chainC k)
graph-chain k = isGraph-ok (chainC k) (g k)
  where
  g : ∀ k → T (isGraph (chainC k))
  g zero    = tt
  g (suc k) = g k

mutual
  low⋆ : ∀ {Γ t B} → Γ ⊢tm t ∶ B → B ≡ ⋆ → LowT Γ t
  low⋆ {Γ} (var-wf {i} _ eq) refl {j} q = mkLow λ e →
    arr≢⋆ (just-inj (trans (sym (subst (λ k → lookup Γ k ≡ _) (∈-single q) e)) eq))
    where
    arr≢⋆ : ∀ {A s t} → arr A s t ≡ ⋆ → ⊥
    arr≢⋆ ()
  low⋆ (coh-wf _ _ _ _ _) ()
  low⋆ (cst-wf {()} _ _) _

  low1 : ∀ {Γ t B a b} → Γ ⊢tm t ∶ B → B ≡ arr ⋆ a b → LowT Γ t
  low1 {Γ} (var-wf {i} _ eq) refl {j} q = mkLow λ e →
    arr≢ (just-inj (trans (sym (subst (λ k → lookup Γ k ≡ _) (∈-single q) e)) eq))
    where
    arr≢ : ∀ {A s t u v a b} → arr (arr A s t) u v ≡ arr ⋆ a b → ⊥
    arr≢ ()
  low1 d@(coh-wf _ _ _ _ s) e with coh-view d e
  ... | cohV k _ _ _ _ _ _ _ = low-sub s (graph-chain k)
  low1 (cst-wf {()} _ _) _

  low-sub : ∀ {Γ τ Δ} → Γ ⊢sub τ ∶ Δ → Graph Δ → LowL Γ (fvSub τ)
  low-sub (⟨⟩-wf _) g ()
  low-sub {Γ} {τ ,ₛ t} {Δ ▸ A} (,-wf sτ d) g =
    low-++ (fvSub τ) (fvTm t) (low-sub sτ (λ i e → g i (lookup-wk Δ i A e))) (go (small {Δ ▸ A} (len Δ) A (lookup-top Δ A) (g (len Δ))) d)
    where
    go : ∀ {A} → Small A → Γ ⊢tm t ∶ A [ τ ]ty → LowT Γ t
    go s⋆       d = low⋆ d refl
    go (s1 a b) d = low1 d refl

-- Coherences over graph contexts (such as chain fillers) are low.
low-coh : ∀ {Γ Θ A σ B} → Γ ⊢tm coh Θ A σ ∶ B → Graph Θ → LowT Γ (coh Θ A σ)
low-coh (coh-wf _ _ _ _ s) g = low-sub s g

-- Vertical composites of low 2-cells are low.
low-vcomp : ∀ {Γ x y t s u c h} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s → Γ ⊢tm h ∶ arr (arr ⋆ x y) s u →
            LowT Γ c → LowT Γ h → LowT Γ (vcomp (arr ⋆ x y) t s u c h)
low-vcomp {x = x} {y} {t} {s} {u} {c} {h} dc dh lc lh =
  low-++ ((sp ++ fvTm c) ++ fvTm u) (fvTm h)
    (low-++ (sp ++ fvTm c) (fvTm u)
      (low-++ sp (fvTm c)
        (low-++ ((([] ++ fvTm x) ++ fvTm y) ++ fvTm t) (fvTm s)
          (low-++ (([] ++ fvTm x) ++ fvTm y) (fvTm t)
            (low-++ ([] ++ fvTm x) (fvTm y) (low-++ [] (fvTm x) low-[] (low⋆ dx refl)) (low⋆ dy refl))
            (low1 dt refl))
          (low1 ds refl))
        lc)
      (low1 du refl))
    lh
  where
  sp = (((([] ++ fvTm x) ++ fvTm y) ++ fvTm t) ++ fvTm s)
  b = bd2 dc
  dx = fst b
  dy = fst (snd b)
  dt = fst (snd (snd b))
  ds = snd (snd (snd b))
  du = snd (snd (snd (bd2 dh)))

------------------------------------------------------------------------
-- The support of a low query is a graph context.

private
  module SP = RC.SupP

  small-ren : ∀ {A} ρ → Small A → Small (A [ ρ ]ty)
  small-ren ρ s⋆       = s⋆
  small-ren ρ (s1 a b) = s1 _ _

  graph-snoc : ∀ {Δ A} → Graph Δ → Small A → Graph (Δ ▸ A)
  graph-snoc {Δ} {A} g sA i e with i ==ℕ len Δ
  graph-snoc {Δ} {⋆}         g s⋆       i () | true
  graph-snoc {Δ} {arr ⋆ a b} g (s1 a b) i () | true
  ... | false = g i e

  low-down : ∀ {Γ A i} → Low (Γ ▸ A) i → Low Γ i
  low-down {Γ} {A} {i} l = mkLow λ e → unLow l (lookup-wk Γ i A e)

  low-up : ∀ {Γ A i} → (i ==ℕ len Γ) ≡ false → Low Γ i → Low (Γ ▸ A) i
  low-up {Γ} {A} {i} ne l = mkLow (go ne)
    where
    go : (i ==ℕ len Γ) ≡ false → ∀ {B s t u v} → lookup (Γ ▸ A) i ≡ just (arr (arr B s t) u v) → ⊥
    go ne e rewrite ne = unLow l e

  low-top : ∀ {Γ A} → Small A → Low (Γ ▸ A) (len Γ)
  low-top {Γ} {⋆}         s⋆       = mkLow λ e → case (just-inj (trans (sym (lookup-top Γ ⋆)) e))
    where case : ∀ {B s t u v} → ⋆ ≡ arr (arr B s t) u v → ⊥
          case ()
  low-top {Γ} {arr ⋆ a b} (s1 a b) = mkLow λ e → case (just-inj (trans (sym (lookup-top Γ (arr ⋆ a b))) e))
    where case : ∀ {B s t u v} → arr ⋆ a b ≡ arr (arr B s t) u v → ⊥
          case ()

  -- The free variables of a small, well-formed type are low.
  low-ty : ∀ {Γ A} → Γ ⊢ty A → Small A → LowL Γ (fvTy A)
  low-ty _ s⋆ ()
  low-ty {A = arr ⋆ a b} (arr-wf da db) (s1 a b) =
    low-++ ([] ++ fvTm a) (fvTm b) (low-++ [] (fvTm a) low-[] (low⋆ da refl)) (low⋆ db refl)

  lk-hit′ : ∀ Γ A i → (i ==ℕ len Γ) ≡ true → lookup (Γ ▸ A) i ≡ just A
  lk-hit′ Γ A i e rewrite e = refl

  n≮n : ∀ n → T (n <ℕ n) → ⊥
  n≮n zero    ()
  n≮n (suc n) p = n≮n n p

  ==-true : ∀ i n → (i ==ℕ n) ≡ true → i ≡ n
  ==-true i n e = ==ℕ-sound i n (subst T (sym e) tt)

graph-restr : ∀ keep Γ → (∀ i → T (keep i) → Low Γ i) → Graph (SP.Restr.rctx (SP.restr keep Γ))
graph-restr keep ε       h i ()
graph-restr keep (Γ ▸ A) h with keep (len Γ) in e
... | true  = graph-snoc (graph-restr keep Γ (λ i k → low-down (h i k)))
                (small-ren (SP.Restr.ren (SP.restr keep Γ))
                  (small {Γ ▸ A} (len Γ) A (lookup-top Γ A) (unLow (h (len Γ) (subst T (sym e) tt)))))
... | false = graph-restr keep Γ (λ i k → low-down (h i k))

-- Every variable of the support closure of a low set is low.
kept-low : ∀ {Γ} → Γ ⊢ctx → ∀ S → LowL Γ S → LowL Γ (SP.close Γ S)
kept-low ε-wf S hS q = hS q
kept-low {Γ ▸ A} (▸-wf w a) S hS {i} q with elem (len Γ) S in eS
... | true  = up (kept-low w (fvTy A ++ S) (low-++ (fvTy A) S (low-ty a sA) (λ r → low-down (hS r))) q)
  where
  sA = small {Γ ▸ A} (len Γ) A (lookup-top Γ A) (unLow (hS (subst T (sym eS) tt)))
  up : Low Γ i → Low (Γ ▸ A) i
  up l with i ==ℕ len Γ in ei
  ... | true  = mkLow λ e → unLow (low-top {Γ} {A} sA) (trans (lookup-top Γ A) (trans (sym (lk-hit′ Γ A i ei)) e))
  ... | false = low-up ei l
... | false = up (kept-low w S (λ r → low-down (hS r)) q)
  where
  up : Low Γ i → Low (Γ ▸ A) i
  up l with i ==ℕ len Γ in ei
  ... | true  = hS (SP.close-big closed w S i
                     (λ p → n≮n (len Γ) (subst (λ j → T (j <ℕ len Γ)) (==-true i (len Γ) ei) p)) q)
                     
  ... | false = low-up ei l

graph-supp : ∀ {Γ A t u} (dt : Γ ⊢tm t ∶ A) (du : Γ ⊢tm u ∶ A) → LowL Γ (SP.supp closed A t u) →
             Graph (RC.Sup.Γ′ dt du)
graph-supp {Γ} {A} {t} {u} dt du h =
  graph-restr (SP.keepOf closed Γ A t u) Γ (λ i k → kept-low (tm-ctx dt) (SP.supp closed A t u) h k)

------------------------------------------------------------------------
-- Two parallel low 2-cells are connected.

cancel : ∀ {Γ x y p q u v} (du : Γ ⊢tm u ∶ arr (arr ⋆ x y) p q) (dv : Γ ⊢tm v ∶ arr (arr ⋆ x y) p q) →
         LowT Γ u → LowT Γ v → Ans Γ (arr (arr ⋆ x y) p q) u v
cancel {Γ} {x} {y} {p} {q} {u} {v} du dv lu lv =
  from-just (RC.rcS du dv) {RC.rcS-graphSupp du dv (graph-supp du dv hS)}
  where
  pq = bd3 du
  b = bd2 du
  lA : LowL Γ (fvTy (arr (arr ⋆ x y) p q))
  lA = low-++ (fvTy (arr ⋆ x y)) (fvTm p ++ fvTm q)
         (low-++ ([] ++ fvTm x) (fvTm y) (low-++ [] (fvTm x) low-[] (low⋆ (fst b) refl)) (low⋆ (fst (snd b)) refl))
         (low-++ (fvTm p) (fvTm q) (low1 (fst pq) refl) (low1 (snd pq) refl))
  hS : LowL Γ (SP.supp closed (arr (arr ⋆ x y) p q) u v)
  hS = low-++ (fvTy (arr (arr ⋆ x y) p q)) (fvTm u ++ fvTm v) lA (low-++ (fvTm u) (fvTm v) lu lv)
