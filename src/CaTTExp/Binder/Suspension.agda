------------------------------------------------------------------------
-- Suspension for the kernel with operation heads (ledger S27 (c);
-- spec §1.5).
--
-- Σ adds two objects N (level 0) and S (level 1) in front of a context
-- and raises every dimension by one, as in CaTTExp.Suspension. A
-- coherence over Θ becomes a coherence over ΣΘ. A head h[σ] becomes
-- (Σh)[Σσ], where Σh is a head the signature provides with arity
-- Σ(Γ_h) and type Σ(A_h) (spec §1.5: "a head suspends when the
-- signature also gives its suspension").
--
--   Γ ⊢ctx        implies  ΣΓ ⊢ctx
--   Γ ⊢ty A       implies  ΣΓ ⊢ty ΣA
--   Γ ⊢tm t ∶ A   implies  ΣΓ ⊢tm Σt ∶ ΣA
--   Γ ⊢sub σ ∶ Δ  implies  ΣΓ ⊢sub Σσ ∶ ΣΔ
--
-- for plain CaTT's side condition, every mark judgment that suspension
-- preserves (`MarkΣ`; proved for rule (MARK) alone, `varMarkΣ`), and
-- syntax that is *suspendable* (`sokTm` etc.): every binder in it is a
-- head at which `canΣ` holds (in particular its telescope is empty),
-- coherence bodies included, and it has no closed constant of the old
-- kind (`cst`). A constant that should suspend is entered as a head
-- with empty arity (spec §1.1: c abbreviates c[⟨⟩]); its suspension
-- is then a head with arity (N, S : ⋆). With canΣ false everywhere
-- this is CaTTExp.Suspension's constant-free hypothesis.
--
-- Hypotheses on the signature (`HeadSusp`): at every suspendable
-- head b, selector y (with its side condition), b is honest
-- (CaTTExp.Binder.HonestHeads) with arity G and type A, the head
-- sH b y at selector sY b y is honest with arity ΣG and type ΣA, its
-- side condition holds, and G and A are suspendable syntax.
--
-- Pasting contexts are pure (CaTTExp.Binder.Pasting), so their
-- boundary computations are transferred from CaTTExp.Suspension along
-- the embedding of pure syntax.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Pure as P
import CaTTExp.Pasting
import CaTTExp.Suspension

module CaTTExp.Binder.Suspension
  (𝕊 : Signature)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  (canΣ : Signature.B 𝕊 → Nat → Bool)
  (sH : Signature.B 𝕊 → Nat → Signature.B 𝕊)
  (sY : Signature.B 𝕊 → Nat → Nat)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B
open import CaTTExp.Binder.Typing 𝕊 using (isCoh; isOp; cattSide)
open import CaTTExp.Binder.TypingWith 𝕊 cattSide mark
open import CaTTExp.Binder.Scoping 𝕊 cattSide mark using (args-lc; sub-lc)
open import CaTTExp.Binder.HonestHeads 𝕊
module PS = CaTTExp.Suspension P.∅
open PS using (Mem; LMem; _⊎_; inj₁; inj₂; lift-≈; Lift; S)
open CaTTExp.Pasting P.∅ using () renaming (_⊢ps to _⊢ps₀; _⊢ps_∶_ to _⊢ps₀_∶_)

------------------------------------------------------------------------
-- The operation.

mutual
  Σty : Ty → Ty
  Σty ⋆           = arr ⋆ (var 0) (var 1)
  Σty (arr A t u) = arr (Σty A) (Σtm t) (Σtm u)

  Σtm : Tm → Tm
  Σtm (var i)       = var (S i)
  Σtm (bvar d j)    = bvar d j
  Σtm (coh Θ A τ)   = coh (Σctx Θ) (Σty A) (Σsub τ)
  Σtm (cst k)       = cst k
  Σtm (bnd b y Δ τ) = bnd (sH b y) (sY b y) Δ (Σsub τ)

  Σsub : Sub → Sub
  Σsub ⟨⟩       = ⟨⟩ ,ₛ var 0 ,ₛ var 1
  Σsub (τ ,ₛ t) = Σsub τ ,ₛ Σtm t

  Σctx : Ctx → Ctx
  Σctx ε             = ε ▸ ⋆ ▸ ⋆
  Σctx (Γ ▸[ ms ] A) = Σctx Γ ▸[ ms ] Σty A

-- Suspendable syntax.
isε : Ctx → Bool
isε ε = true
isε _ = false

mutual
  sokTy : Ty → Bool
  sokTy ⋆           = true
  sokTy (arr A t u) = sokTy A ∧ sokTm t ∧ sokTm u

  sokTm : Tm → Bool
  sokTm (var _)       = true
  sokTm (bvar _ _)    = true
  sokTm (coh Θ A τ)   = sokCtx Θ ∧ sokTy A ∧ sokSub τ
  sokTm (cst _)       = false
  sokTm (bnd b y Δ τ) = canΣ b y ∧ isε Δ ∧ sokSub τ

  sokSub : Sub → Bool
  sokSub ⟨⟩       = true
  sokSub (τ ,ₛ t) = sokSub τ ∧ sokTm t

  sokCtx : Ctx → Bool
  sokCtx ε             = true
  sokCtx (Γ ▸[ _ ] A) = sokCtx Γ ∧ sokTy A

isε-≡ : ∀ Δ → T (isε Δ) → Δ ≡ ε
isε-≡ ε _ = refl

------------------------------------------------------------------------
-- Hypotheses.

record HeadSusp : Set where
  field
    arity : ∀ b y → T (canΣ b y) → T (bside b y ε) →
            Σ Ctx λ G → Σ Ty λ A →
              HonestAt b y G A × HonestAt (sH b y) (sY b y) (Σctx G) (Σty A)
              × T (bside (sH b y) (sY b y) ε) × T (sokCtx G) × T (sokTy A)

-- The mark judgment is preserved by suspension.
MarkΣ : Set
MarkΣ = ∀ {Γ t A m} → Γ ⊢tm t ∶ A → T (sokTm t) → T (mark Γ m t) →
        T (mark (Σctx Γ) m (Σtm t))

------------------------------------------------------------------------
-- Lengths and lookups.

lenΣ : ∀ Γ → len (Σctx Γ) ≡ S (len Γ)
lenΣ ε             = refl
lenΣ (Γ ▸[ _ ] A) = cong suc (lenΣ Γ)

lenₛΣ : ∀ σ → lenₛ (Σsub σ) ≡ S (lenₛ σ)
lenₛΣ ⟨⟩       = refl
lenₛΣ (σ ,ₛ t) = cong suc (lenₛΣ σ)

dimΣ : ∀ A → dim (Σty A) ≡ suc (dim A)
dimΣ ⋆           = refl
dimΣ (arr A t u) = cong suc (dimΣ A)

lookupΣ : ∀ Γ i {A} → lookup Γ i ≡ just A → lookup (Σctx Γ) (S i) ≡ just (Σty A)
lookupΣ (Γ ▸[ _ ] B) i eq rewrite lenΣ Γ with i ==ℕ len Γ
... | true  = cong (λ X → just (Σty X)) (just-inj eq)
... | false = lookupΣ Γ i eq

marksAtΣ : ∀ Γ i → marksAt (Σctx Γ) (S i) ≡ marksAt Γ i
marksAtΣ ε             i = refl
marksAtΣ (Γ ▸[ ms ] B) i rewrite lenΣ Γ with i ==ℕ len Γ
... | true  = refl
... | false = marksAtΣ Γ i

lookupΣ-N : ∀ Γ → lookup (Σctx Γ) 0 ≡ just ⋆
lookupΣ-N ε             = refl
lookupΣ-N (Γ ▸[ _ ] A) rewrite lenΣ Γ = lookupΣ-N Γ

lookupΣ-S : ∀ Γ → lookup (Σctx Γ) 1 ≡ just ⋆
lookupΣ-S ε             = refl
lookupΣ-S (Γ ▸[ _ ] A) rewrite lenΣ Γ = lookupΣ-S Γ

marksΣ-N : ∀ Γ → marksAt (Σctx Γ) 0 ≡ []
marksΣ-N ε             = refl
marksΣ-N (Γ ▸[ _ ] A) rewrite lenΣ Γ = marksΣ-N Γ

marksΣ-S : ∀ Γ → marksAt (Σctx Γ) 1 ≡ []
marksΣ-S ε             = refl
marksΣ-S (Γ ▸[ _ ] A) rewrite lenΣ Γ = marksΣ-S Γ

lookupₛΣ : ∀ σ i → lookupₛ (Σsub σ) (S i) ≡ Σtm (lookupₛ σ i)
lookupₛΣ ⟨⟩       i = refl
lookupₛΣ (σ ,ₛ t) i rewrite lenₛΣ σ with i ==ℕ lenₛ σ
... | true  = refl
... | false = lookupₛΣ σ i

lookupₛΣ-N : ∀ σ → lookupₛ (Σsub σ) 0 ≡ var 0
lookupₛΣ-N ⟨⟩       = refl
lookupₛΣ-N (σ ,ₛ t) rewrite lenₛΣ σ = lookupₛΣ-N σ

lookupₛΣ-S : ∀ σ → lookupₛ (Σsub σ) 1 ≡ var 1
lookupₛΣ-S ⟨⟩       = refl
lookupₛΣ-S (σ ,ₛ t) rewrite lenₛΣ σ = lookupₛΣ-S σ

------------------------------------------------------------------------
-- Suspension commutes with substitution (on suspendable syntax: a
-- head's telescope is empty, so the substitution has nothing to act on
-- there).

mutual
  Σty[] : ∀ A σ → T (sokTy A) → Σty (A [ σ ]ty) ≡ Σty A [ Σsub σ ]ty
  Σty[] ⋆           σ _ = sym (cong₂ (arr ⋆) (lookupₛΣ-N σ) (lookupₛΣ-S σ))
  Σty[] (arr A t u) σ p =
    let (a , q) = T∧ {sokTy A} p ; (b , c) = T∧ {sokTm t} q in
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (Σty[] A σ a) (cong₂ _,_ (Σtm[] t σ b) (Σtm[] u σ c))

  Σtm[] : ∀ t σ → T (sokTm t) → Σtm (t [ σ ]tm) ≡ Σtm t [ Σsub σ ]tm
  Σtm[] (var i)       σ _ = sym (lookupₛΣ σ i)
  Σtm[] (bvar d j)    σ _ = refl
  Σtm[] (coh Θ A τ)   σ p =
    let (_ , q) = T∧ {sokCtx Θ} p ; (_ , c) = T∧ {sokTy A} q in
    cong (coh (Σctx Θ) (Σty A)) (Σsub∘ τ σ c)
  Σtm[] (cst k)       σ ()
  Σtm[] (bnd b y Δ τ) σ p =
    let (_ , q) = T∧ {canΣ b y} p ; (e , c) = T∧ {isε Δ} q in
    go Δ (isε-≡ Δ e) c
    where
    go : ∀ Δ → Δ ≡ ε → T (sokSub τ) →
         bnd (sH b y) (sY b y) (Δ [ σ ]tel) (Σsub (τ ∘ σ))
           ≡ bnd (sH b y) (sY b y) (Δ [ Σsub σ ]tel) (Σsub τ ∘ Σsub σ)
    go .ε refl c = cong (bnd (sH b y) (sY b y) ε) (Σsub∘ τ σ c)

  Σsub∘ : ∀ τ σ → T (sokSub τ) → Σsub (τ ∘ σ) ≡ Σsub τ ∘ Σsub σ
  Σsub∘ ⟨⟩       σ _ = sym (cong₂ (λ a b → ⟨⟩ ,ₛ a ,ₛ b) (lookupₛΣ-N σ) (lookupₛΣ-S σ))
  Σsub∘ (τ ,ₛ t) σ p =
    let (a , b) = T∧ {sokSub τ} p in cong₂ _,ₛ_ (Σsub∘ τ σ a) (Σtm[] t σ b)

------------------------------------------------------------------------
-- Pure syntax: suspension commutes with the embedding, and pasting
-- contexts suspend.


mutual
  Σ-embTy : ∀ A → Σty (embTy A) ≡ embTy (PS.Σty A)
  Σ-embTy P.⋆           = refl
  Σ-embTy (P.arr A t u) =
    cong₂ (λ X (Y : Tm × Tm) → arr X (fst Y) (snd Y))
      (Σ-embTy A) (cong₂ _,_ (Σ-embTm t) (Σ-embTm u))

  Σ-embTm : ∀ t → Σtm (embTm t) ≡ embTm (PS.Σtm t)
  Σ-embTm (P.var i)     = refl
  Σ-embTm (P.coh Θ A τ) =
    cong₂ (λ X (Y : Ty × Sub) → coh X (fst Y) (snd Y))
      (Σ-embCtx Θ) (cong₂ _,_ (Σ-embTy A) (Σ-embSub τ))
  Σ-embTm (P.cst ())

  Σ-embCtx : ∀ Γ → Σctx (embCtx Γ) ≡ embCtx (PS.Σctx Γ)
  Σ-embCtx P.ε       = refl
  Σ-embCtx (Γ P.▸ A) = cong₂ _▸_ (Σ-embCtx Γ) (Σ-embTy A)

  Σ-embSub : ∀ σ → Σsub (embSub σ) ≡ embSub (PS.Σsub σ)
  Σ-embSub P.⟨⟩       = refl
  Σ-embSub (σ P.,ₛ t) = cong₂ _,ₛ_ (Σ-embSub σ) (Σ-embTm t)

private
  ps-inner : ∀ {Γ₀} → Γ₀ ⊢ps₀ → Σ Nat λ x → Γ₀ ⊢ps₀ x ∶ P.⋆
  ps-inner (CaTTExp.Pasting.ps d) = _ , d

Σps : ∀ {Θ} → Θ ⊢ps → Σctx Θ ⊢ps
Σps {Θ} (Θ₀ , e , p) with ps-inner (PS.Σps′ p)
... | _ , d′ =
  PS.Σctx Θ₀
  , subst (λ X → toPure X ≡ just (PS.Σctx Θ₀))
          (trans (sym (Σ-embCtx Θ₀)) (cong Σctx (toPure-sound Θ e)))
          (toPure-ps d′)
  , PS.Σps′ p

-- Boundaries, dimension and lengths of embedded contexts.
private
  dim-emb : ∀ A → dim (embTy A) ≡ P.dim A
  dim-emb P.⋆           = refl
  dim-emb (P.arr A _ _) = cong suc (dim-emb A)

  len-emb : ∀ Γ → len (embCtx Γ) ≡ P.len Γ
  len-emb P.ε       = refl
  len-emb (Γ P.▸ _) = cong suc (len-emb Γ)

  dimCtx-emb : ∀ Γ → dimCtx (embCtx Γ) ≡ P.dimCtx Γ
  dimCtx-emb P.ε       = refl
  dimCtx-emb (Γ P.▸ A) rewrite dim-emb A | dimCtx-emb Γ = refl

  src-emb : ∀ i Γ → srcVars i (embCtx Γ) ≡ P.srcVars i Γ
  src-emb i P.ε             = refl
  src-emb i (P.ε P.▸ A)     = refl
  src-emb i (Γ P.▸ A P.▸ B) rewrite dim-emb A | len-emb Γ | src-emb i Γ = refl

  dl-eq : ∀ xs → dropLastᴸ xs ≡ P.dropLastᴸ xs
  dl-eq []           = refl
  dl-eq (x ∷ [])     = refl
  dl-eq (x ∷ y ∷ xs) = cong (x ∷_) (dl-eq (y ∷ xs))

  tgt-emb : ∀ i Γ → tgtVars i (embCtx Γ) ≡ P.tgtVars i Γ
  tgt-emb i P.ε             = refl
  tgt-emb i (P.ε P.▸ A)     = refl
  tgt-emb i (Γ P.▸ A P.▸ B)
    rewrite dim-emb A | len-emb Γ | tgt-emb i Γ | dl-eq (P.tgtVars i Γ) = refl

  ∂⁻-emb : ∀ Γ → ∂⁻ (embCtx Γ) ≡ P.∂⁻ Γ
  ∂⁻-emb Γ rewrite dimCtx-emb Γ = src-emb _ Γ

  ∂⁺-emb : ∀ Γ → ∂⁺ (embCtx Γ) ≡ P.∂⁺ Γ
  ∂⁺-emb Γ rewrite dimCtx-emb Γ = tgt-emb _ Γ

------------------------------------------------------------------------
-- Free variables of suspended syntax.

open PS using (mem++; mem++l; mem++r; mem-single; mem-here; mem-cons; LMem-map; Lift→; Lift←)

mutual
  fvΣty→ : ∀ A n → T (sokTy A) → Mem n (fvTy (Σty A)) → LMem n (fvTy A)
  fvΣty→ ⋆ n _ p with mem-cons n 0 (1 ∷ []) p
  ... | inj₁ e = inj₁ e
  ... | inj₂ q = inj₂ (inj₁ (mem-single n 1 q))
  fvΣty→ (arr A t u) n s p with T∧ {sokTy A} s
  ... | (sA , s′) with T∧ {sokTm t} s′
  ...   | (st , su) with mem++ n (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) p
  ...     | inj₁ q = LMem-map (fvTy A) (fvTy (arr A t u))
                       (λ m r → mem++l m (fvTy A) (fvTm t ++ fvTm u) r) (fvΣty→ A n sA q)
  ...     | inj₂ q with mem++ n (fvTm (Σtm t)) (fvTm (Σtm u)) q
  ...       | inj₁ r = LMem-map (fvTm t) (fvTy (arr A t u))
                         (λ m r′ → mem++r m (fvTy A) (fvTm t ++ fvTm u) (mem++l m (fvTm t) (fvTm u) r′))
                         (fvΣtm→ t n st r)
  ...       | inj₂ r = LMem-map (fvTm u) (fvTy (arr A t u))
                         (λ m r′ → mem++r m (fvTy A) (fvTm t ++ fvTm u) (mem++r m (fvTm t) (fvTm u) r′))
                         (fvΣtm→ u n su r)

  fvΣtm→ : ∀ t n → T (sokTm t) → Mem n (fvTm (Σtm t)) → LMem n (fvTm t)
  fvΣtm→ (var i)       n _ p = inj₂ (inj₂ (i , mem-single n (S i) p , mem-here i []))
  fvΣtm→ (bvar _ _)    n _ ()
  fvΣtm→ (coh Θ A τ)   n s p =
    let (_ , q) = T∧ {sokCtx Θ} s ; (_ , c) = T∧ {sokTy A} q in fvΣsub→ τ n c p
  fvΣtm→ (cst k)       n () _
  fvΣtm→ (bnd b y Δ τ) n s p with T∧ {canΣ b y} s
  ... | (_ , q) with T∧ {isε Δ} q
  ...   | (e , c) with isε-≡ Δ e
  ...     | refl = fvΣsub→ τ n c p

  fvΣsub→ : ∀ σ n → T (sokSub σ) → Mem n (fvSub (Σsub σ)) → LMem n (fvSub σ)
  fvΣsub→ ⟨⟩ n _ p with mem-cons n 0 (1 ∷ []) p
  ... | inj₁ e = inj₁ e
  ... | inj₂ q = inj₂ (inj₁ (mem-single n 1 q))
  fvΣsub→ (σ ,ₛ t) n s p with T∧ {sokSub σ} s
  ... | (sσ , st) with mem++ n (fvSub (Σsub σ)) (fvTm (Σtm t)) p
  ...   | inj₁ q = LMem-map (fvSub σ) (fvSub (σ ,ₛ t)) (λ m r → mem++l m (fvSub σ) (fvTm t) r) (fvΣsub→ σ n sσ q)
  ...   | inj₂ q = LMem-map (fvTm t) (fvSub (σ ,ₛ t)) (λ m r → mem++r m (fvSub σ) (fvTm t) r) (fvΣtm→ t n st q)

mutual
  fvΣty-low : ∀ A n → (n ≡ 0) ⊎ (n ≡ 1) → Mem n (fvTy (Σty A))
  fvΣty-low ⋆ .0 (inj₁ refl) = tt
  fvΣty-low ⋆ .1 (inj₂ refl) = tt
  fvΣty-low (arr A t u) n e = mem++l n (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) (fvΣty-low A n e)

  fvΣty← : ∀ A m → T (sokTy A) → Mem m (fvTy A) → Mem (S m) (fvTy (Σty A))
  fvΣty← (arr A t u) m s p with T∧ {sokTy A} s
  ... | (sA , s′) with T∧ {sokTm t} s′
  ...   | (st , su) with mem++ m (fvTy A) (fvTm t ++ fvTm u) p
  ...     | inj₁ q = mem++l (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u)) (fvΣty← A m sA q)
  ...     | inj₂ q with mem++ m (fvTm t) (fvTm u) q
  ...       | inj₁ r = mem++r (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u))
                         (mem++l (S m) (fvTm (Σtm t)) (fvTm (Σtm u)) (fvΣtm← t m st r))
  ...       | inj₂ r = mem++r (S m) (fvTy (Σty A)) (fvTm (Σtm t) ++ fvTm (Σtm u))
                         (mem++r (S m) (fvTm (Σtm t)) (fvTm (Σtm u)) (fvΣtm← u m su r))

  fvΣtm← : ∀ t m → T (sokTm t) → Mem m (fvTm t) → Mem (S m) (fvTm (Σtm t))
  fvΣtm← (var i)       m _ p = subst (λ k → Mem (S k) (S i ∷ [])) (sym (mem-single m i p)) (mem-here (S i) [])
  fvΣtm← (bvar _ _)    m _ ()
  fvΣtm← (coh Θ A τ)   m s p =
    let (_ , q) = T∧ {sokCtx Θ} s ; (_ , c) = T∧ {sokTy A} q in fvΣsub← τ m c p
  fvΣtm← (cst k)       m () _
  fvΣtm← (bnd b y Δ τ) m s p with T∧ {canΣ b y} s
  ... | (_ , q) with T∧ {isε Δ} q
  ...   | (e , c) with isε-≡ Δ e
  ...     | refl = fvΣsub← τ m c p

  fvΣsub← : ∀ σ m → T (sokSub σ) → Mem m (fvSub σ) → Mem (S m) (fvSub (Σsub σ))
  fvΣsub← (σ ,ₛ t) m s p with T∧ {sokSub σ} s
  ... | (sσ , st) with mem++ m (fvSub σ) (fvTm t) p
  ...   | inj₁ q = mem++l (S m) (fvSub (Σsub σ)) (fvTm (Σtm t)) (fvΣsub← σ m sσ q)
  ...   | inj₂ q = mem++r (S m) (fvSub (Σsub σ)) (fvTm (Σtm t)) (fvΣtm← t m st q)

fvΣ→ : ∀ t A → T (sokTm t) → T (sokTy A) → ∀ n → Mem n (fvTmTy (Σtm t) (Σty A)) → LMem n (fvTmTy t A)
fvΣ→ t A st sA n p with mem++ n (fvTm (Σtm t)) (fvTy (Σty A)) p
... | inj₁ q = LMem-map (fvTm t) (fvTmTy t A) (λ m r → mem++l m (fvTm t) (fvTy A) r) (fvΣtm→ t n st q)
... | inj₂ q = LMem-map (fvTy A) (fvTmTy t A) (λ m r → mem++r m (fvTm t) (fvTy A) r) (fvΣty→ A n sA q)

fvΣ← : ∀ t A → T (sokTm t) → T (sokTy A) → ∀ n → LMem n (fvTmTy t A) → Mem n (fvTmTy (Σtm t) (Σty A))
fvΣ← t A st sA n (inj₁ e)        = mem++r n (fvTm (Σtm t)) _ (fvΣty-low A n (inj₁ e))
fvΣ← t A st sA n (inj₂ (inj₁ e)) = mem++r n (fvTm (Σtm t)) _ (fvΣty-low A n (inj₂ e))
fvΣ← t A st sA .(S m) (inj₂ (inj₂ (m , refl , p))) with mem++ m (fvTm t) _ p
... | inj₁ q = mem++l (S m) (fvTm (Σtm t)) _ (fvΣtm← t m st q)
... | inj₂ q = mem++r (S m) (fvTm (Σtm t)) _ (fvΣty← A m sA q)

------------------------------------------------------------------------
-- The side condition is preserved.

private
  df-eq : ∀ k → downFrom k ≡ P.downFrom k
  df-eq zero    = refl
  df-eq (suc k) = cong (k ∷_) (df-eq k)

  memDown : ∀ n k → Mem n (downFrom k) → T (n <ℕ k)
  memDown n k p = PS.memDown n k (subst (Mem n) (df-eq k) p)

  downMem : ∀ n k → T (n <ℕ k) → Mem n (downFrom k)
  downMem n k p = subst (Mem n) (sym (df-eq k)) (PS.downMem n k p)

  vars→ : ∀ Γ n → Mem n (varsCtx (Σctx Γ)) → LMem n (varsCtx Γ)
  vars→ Γ zero          _ = inj₁ refl
  vars→ Γ (suc zero)    _ = inj₂ (inj₁ refl)
  vars→ Γ (suc (suc m)) p =
    inj₂ (inj₂ (m , refl , downMem m (len Γ)
      (subst (λ k → T (S m <ℕ k)) (lenΣ Γ) (memDown (S m) (len (Σctx Γ)) p))))

  vars← : ∀ Γ n → LMem n (varsCtx Γ) → Mem n (varsCtx (Σctx Γ))
  vars← Γ .0 (inj₁ refl) = downMem 0 (len (Σctx Γ)) (subst (λ k → T (0 <ℕ k)) (sym (lenΣ Γ)) tt)
  vars← Γ .1 (inj₂ (inj₁ refl)) = downMem 1 (len (Σctx Γ)) (subst (λ k → T (1 <ℕ k)) (sym (lenΣ Γ)) tt)
  vars← Γ .(S m) (inj₂ (inj₂ (m , refl , p))) =
    downMem (S m) (len (Σctx Γ)) (subst (λ k → T (S m <ℕ k)) (sym (lenΣ Γ)) (memDown m (len Γ) p))

  and : ∀ {a b} → T a → T b → T (a ∧ b)
  and {true} _ q = q

  Lift-eq→ : ∀ {X Xs} → Xs ≡ Lift X → ∀ n → Mem n Xs → LMem n X
  Lift-eq→ {X} refl n p = Lift→ n X p

  Lift-eq← : ∀ {X Xs} → Xs ≡ Lift X → ∀ n → LMem n X → Mem n Xs
  Lift-eq← {X} refl n p = Lift← n X p

  isCohΣ : ∀ Θ A t u → T (sokTy A) → T (sokTm t) → T (sokTm u) →
           T (isCoh Θ A t u) → T (isCoh (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  isCohΣ Θ A t u sA st su p = and {≈? (fvTmTy (Σtm t) (Σty A)) (varsCtx (Σctx Θ))}
    (lift-≈ (fvTmTy t A) (varsCtx Θ) (fvTmTy (Σtm t) (Σty A)) (varsCtx (Σctx Θ))
            (∧-fst p) (fvΣ→ t A st sA) (fvΣ← t A st sA) (vars→ Θ) (vars← Θ))
    (lift-≈ (fvTmTy u A) (varsCtx Θ) (fvTmTy (Σtm u) (Σty A)) (varsCtx (Σctx Θ))
            (∧-snd {≈? (fvTmTy t A) (varsCtx Θ)} p)
            (fvΣ→ u A su sA) (fvΣ← u A su sA) (vars→ Θ) (vars← Θ))

  -- Boundaries of a suspended pasting context (transferred from pure
  -- syntax).
  bdΣ : ∀ {Θ₀} → Θ₀ ⊢ps₀ → ∀ k → P.dimCtx Θ₀ ≡ suc k →
        (∂⁻ (Σctx (embCtx Θ₀)) ≡ Lift (∂⁻ (embCtx Θ₀))) × (∂⁺ (Σctx (embCtx Θ₀)) ≡ Lift (∂⁺ (embCtx Θ₀)))
  bdΣ {Θ₀} (CaTTExp.Pasting.ps d) k e
    rewrite Σ-embCtx Θ₀ | ∂⁻-emb (PS.Σctx Θ₀) | ∂⁺-emb (PS.Σctx Θ₀) | ∂⁻-emb Θ₀ | ∂⁺-emb Θ₀ =
    src , tgt
    where
    o = PS.ps-odd d
    dimeq : P.dimCtx (PS.Σctx Θ₀) ∸ 1 ≡ suc (P.dimCtx Θ₀ ∸ 1)
    dimeq rewrite PS.dimCtxΣ Θ₀ o | e = refl
    src : P.∂⁻ (PS.Σctx Θ₀) ≡ Lift (P.∂⁻ Θ₀)
    src rewrite dimeq = PS.srcΣ (P.dimCtx Θ₀ ∸ 1) Θ₀
    tgt : P.∂⁺ (PS.Σctx Θ₀) ≡ Lift (P.∂⁺ Θ₀)
    tgt rewrite dimeq = PS.tgtΣ (P.dimCtx Θ₀ ∸ 1) Θ₀ o

  isOpΣ : ∀ Θ A t u → Θ ⊢ps → ∀ k → dimCtx Θ ≡ suc k →
          T (sokTy A) → T (sokTm t) → T (sokTm u) →
          T (isOp Θ A t u) → T (isOp (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  isOpΣ Θ A t u (Θ₀ , e₀ , p₀) k e sA st su p
    with toPure-sound Θ e₀
  ... | refl =
    and {≈? (fvTmTy (Σtm t) (Σty A)) (∂⁻ (Σctx Θ))}
      (lift-≈ (fvTmTy t A) (∂⁻ Θ) (fvTmTy (Σtm t) (Σty A)) (∂⁻ (Σctx Θ))
              (∧-fst p) (fvΣ→ t A st sA) (fvΣ← t A st sA) (Lift-eq→ src) (Lift-eq← src))
      (lift-≈ (fvTmTy u A) (∂⁺ Θ) (fvTmTy (Σtm u) (Σty A)) (∂⁺ (Σctx Θ))
              (∧-snd {≈? (fvTmTy t A) (∂⁻ Θ)} p)
              (fvΣ→ u A su sA) (fvΣ← u A su sA) (Lift-eq→ tgt) (Lift-eq← tgt))
    where
    e′ : P.dimCtx Θ₀ ≡ suc k
    e′ = trans (sym (dimCtx-emb Θ₀)) e
    src = fst (bdΣ p₀ k e′)
    tgt = snd (bdΣ p₀ k e′)

  ∨-elim : ∀ {a b} {X : Set} → T (a ∨ b) → (T a → X) → (T b → X) → X
  ∨-elim {true}          p f g = f tt
  ∨-elim {false} {true}  p f g = g tt

  ∨-inl : ∀ {a b} → T a → T (a ∨ b)
  ∨-inl {true} _ = tt

  ∨-inr : ∀ {a b} → T b → T (a ∨ b)
  ∨-inr {true}  _ = tt
  ∨-inr {false} p = p

  -- A pasting context of dimension 0 is the point, where an operation
  -- is a full coherence.
  dim0-point : ∀ {Θ} → Θ ⊢ps → dimCtx Θ ≡ 0 → Θ ≡ ε ▸ ⋆
  dim0-point {Θ} (Θ₀ , e₀ , CaTTExp.Pasting.ps d) e
    with toPure-sound Θ e₀
  ... | refl rewrite PS.ps-dim0 d (trans (sym (dimCtx-emb Θ₀)) e) = refl

sideΣ : ∀ {Θ A t u} → Θ ⊢ps → T (sokTy A) → T (sokTm t) → T (sokTm u) →
        T (cattSide Θ A t u) → T (cattSide (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
sideΣ {Θ} {A} {t} {u} ps′ sA st su p = go (dimCtx Θ) refl
  where
  go : ∀ n → dimCtx Θ ≡ n → T (cattSide (Σctx Θ) (Σty A) (Σtm t) (Σtm u))
  go zero e =
    ∨-inl (isCohΣ Θ A t u sA st su
      (subst (λ Γ → T (cattSide Γ A t u) → T (isCoh Γ A t u)) (sym (dim0-point {Θ} ps′ e))
             (λ q → ∨-elim {isCoh (ε ▸ ⋆) A t u} {isOp (ε ▸ ⋆) A t u} q (λ c → c) (λ o → o)) p))
  go (suc k) e = ∨-elim p (λ c → ∨-inl (isCohΣ Θ A t u sA st su c))
                          (λ o → ∨-inr (isOpΣ Θ A t u ps′ k e sA st su o))

------------------------------------------------------------------------
-- The theorem.

module _ (hs : HeadSusp) (mΣ : MarkΣ) where

  open HeadSusp hs
  open import CaTTExp.Binder.Presup 𝕊 cattSide mark using (args-ctx; args-len)

  private
    N-wf : ∀ {Γ} → Σctx Γ ⊢ctx → Σctx Γ ⊢ty Σty ⋆
    N-wf {Γ} w = arr-wf (var-wf w (lookupΣ-N Γ)) (var-wf w (lookupΣ-S Γ))

    scTyAt : ∀ {m n} A → m ≡ n → T (scTy? m A) → T (scTy? n A)
    scTyAt A refl p = p

    marksOKΣ : ∀ {Γ t A} ms → Γ ⊢tm t ∶ A → T (sokTm t) →
               T (marksOK Γ ms t) → T (marksOK (Σctx Γ) ms (Σtm t))
    marksOKΣ []       d s _ = tt
    marksOKΣ {Γ} {t} (m ∷ ms) d s p =
      let (a , b) = T∧ {mark Γ m t} p in ∧T (mΣ d s a) (marksOKΣ ms d s b)

    -- The type at an entry of the closed arity, opened with ts, then
    -- suspended, is the suspended type opened with Σts.
    entryΣ : ∀ ts ts′ A → LC ts → LC ts′ → T (sokTy A) →
             T (scTy? (lenₛ ts) A) → T (lcTy? 0 A) →
             T (scTy? (lenₛ ts′) (Σty A)) → T (lcTy? 0 (Σty A)) →
             ts′ ≡ Σsub ts →
             Σty (opTy 0 ts (clTy 0 A)) ≡ opTy 0 ts′ (clTy 0 (Σty A))
    entryΣ ts .(Σsub ts) A l l′ sA scA lcA scA′ lcA′ refl =
      trans (cong Σty (open-clTy 0 ts A l scA lcA))
            (trans (Σty[] A ts sA) (sym (open-clTy 0 (Σsub ts) (Σty A) l′ scA′ lcA′)))

  mutual
    Σctx-wf : ∀ {Γ} → Γ ⊢ctx → T (sokCtx Γ) → Σctx Γ ⊢ctx
    Σctx-wf ε-wf _ = ▸-wf (▸-wf ε-wf (⋆-wf ε-wf)) (⋆-wf (▸-wf ε-wf (⋆-wf ε-wf)))
    Σctx-wf {Γ ▸[ ms ] A} (▸-wf w a) s =
      let (nΓ , nA) = T∧ {sokCtx Γ} s in ▸-wf (Σctx-wf w nΓ) (Σty-wf a nΓ nA)

    Σty-wf : ∀ {Γ A} → Γ ⊢ty A → T (sokCtx Γ) → T (sokTy A) → Σctx Γ ⊢ty Σty A
    Σty-wf (⋆-wf w) nΓ _ = N-wf (Σctx-wf w nΓ)
    Σty-wf {A = arr A t u} (arr-wf d e) nΓ s =
      let (_ , q) = T∧ {sokTy A} s ; (nt , nu) = T∧ {sokTm t} q in
      arr-wf (Σtm-wf d nΓ nt) (Σtm-wf e nΓ nu)

    Σtm-wf : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (sokCtx Γ) → T (sokTm t) → Σctx Γ ⊢tm Σtm t ∶ Σty A
    Σtm-wf {Γ} (var-wf {i} w eq) nΓ _ = var-wf (Σctx-wf w nΓ) (lookupΣ Γ i eq)
    Σtm-wf {Γ} (coh-wf {Θ} {A} {t} {u} {σ} p w a ok s) nΓ n =
      let (nΘ , q) = T∧ {sokCtx Θ} n ; (nB , nσ) = T∧ {sokTy (arr A t u)} q
          (nA , q′) = T∧ {sokTy A} nB ; (nt , nu) = T∧ {sokTm t} q′ in
      subst (Σctx Γ ⊢tm coh (Σctx Θ) (Σty (arr A t u)) (Σsub σ) ∶_)
        (sym (Σty[] (arr A t u) σ nB))
        (coh-wf (Σps {Θ} p) (Σctx-wf w nΘ) (Σty-wf a nΘ nB) (sideΣ {Θ} {A} {t} {u} p nA nt nu ok)
                (Σsub-wf s nΓ nσ nΘ))
    Σtm-wf (cst-wf _ _) _ ()
    Σtm-wf {Γ} (bnd-wf {b} {y} {Δ} {ts} _ _ _ ok as) nΓ n
      with T∧ {canΣ b y} n
    ... | (cb , q) with T∧ {isε Δ} q
    ...   | (eΔ , nts) with isε-≡ Δ eΔ
    ...     | refl with arity b y cb ok
    ...       | (G , A , ha , ha′ , ok′ , nG , nA) =
      subst (Σctx Γ ⊢tm bnd (sH b y) (sY b y) ε (Σsub ts) ∶_) tyeq d′
      where
      Σas : Σctx Γ ⊢args Σsub ts ∶ clTel 0 (Σctx G)
      Σas = Σargs-wf G (HonestAt.honest ha) (HonestAt.honest ha′) nG as (HonestAt.args-eq ha) nΓ nts
      d′ : Σctx Γ ⊢tm bnd (sH b y) (sY b y) ε (Σsub ts) ∶ opTy 0 (Σsub ts) (bres (sH b y) (sY b y) ε)
      d′ = bnd-wf tt tt (args-ctx Σas) ok′
             (subst (Σctx Γ ⊢args Σsub ts ∶_) (sym (HonestAt.args-eq ha′)) Σas)
      lts : lenₛ ts ≡ len G
      lts = trans (args-len as) (trans (cong len (HonestAt.args-eq ha)) (len-clTel 0 G))
      lΣts : lenₛ (Σsub ts) ≡ len (Σctx G)
      lΣts = trans (args-len Σas) (len-clTel 0 (Σctx G))
      tyeq : opTy 0 (Σsub ts) (bres (sH b y) (sY b y) ε) ≡ Σty (opTy 0 ts (bres b y ε))
      tyeq rewrite HonestAt.res-eq ha′ | HonestAt.res-eq ha =
        sym (entryΣ ts (Σsub ts) A (args-lc as) (args-lc Σas) nA
               (scTyAt A (sym lts) (HonestAt.ty-sc ha)) (HonestAt.ty-lc ha)
               (scTyAt (Σty A) (sym lΣts) (HonestAt.ty-sc ha′)) (HonestAt.ty-lc ha′) refl)

    Σsub-wf : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → T (sokCtx Γ) → T (sokSub σ) → T (sokCtx Δ) →
              Σctx Γ ⊢sub Σsub σ ∶ Σctx Δ
    Σsub-wf {Γ} (⟨⟩-wf w) nΓ _ _ =
      ,-wf (,-wf (⟨⟩-wf w′) (var-wf w′ (lookupΣ-N Γ)) tt) (var-wf w′ (lookupΣ-S Γ)) tt
      where
      w′ = Σctx-wf w nΓ
    Σsub-wf {Γ} (,-wf {σ} {Δ} {t} {ms} {A} s d o) nΓ nσt nΔA =
      let (nσ , nt) = T∧ {sokSub σ} nσt ; (nΔ , nA) = T∧ {sokCtx Δ} nΔA in
      ,-wf (Σsub-wf s nΓ nσ nΔ)
           (subst (Σctx Γ ⊢tm Σtm t ∶_) (Σty[] A σ nA) (Σtm-wf d nΓ nt))
           (marksOKΣ ms d nt o)

    -- Arguments for an honest arity G: their suspension (with N and S
    -- in front) are arguments for ΣG.
    Σargs-wf : ∀ {Γ ts Θ} G → Honest G → Honest (Σctx G) → T (sokCtx G) →
               Γ ⊢args ts ∶ Θ → Θ ≡ clTel 0 G → T (sokCtx Γ) → T (sokSub ts) →
               Σctx Γ ⊢args Σsub ts ∶ clTel 0 (Σctx G)
    Σargs-wf {Γ} ε _ _ _ (⟨⟩-a w) refl nΓ _ =
      ,-a (,-a (⟨⟩-a w′) (var-wf w′ (lookupΣ-N Γ)) tt) (var-wf w′ (lookupΣ-S Γ)) tt
      where
      w′ = Σctx-wf w nΓ
    Σargs-wf {Γ} (G ▸[ ms ] A) (hG , sA , lA) (hΣG , sΣA , lΣA) nGA
             (,-a {ts} {t = t} a d o) refl nΓ ntst =
      let (nG , nA) = T∧ {sokCtx G} nGA ; (nts , nt) = T∧ {sokSub ts} ntst
          a′ = Σargs-wf G hG hΣG nG a refl nΓ nts
          lts : lenₛ ts ≡ len G
          lts = trans (args-len a) (len-clTel 0 G)
          lΣts : lenₛ (Σsub ts) ≡ len (Σctx G)
          lΣts = trans (args-len a′) (len-clTel 0 (Σctx G))
      in
      ,-a a′
          (subst (Σctx Γ ⊢tm Σtm t ∶_)
             (entryΣ ts (Σsub ts) A (args-lc a) (args-lc a′) nA
                (scTyAt A (sym lts) sA) lA (scTyAt (Σty A) (sym lΣts) sΣA) lΣA refl)
             (Σtm-wf d nΓ nt))
          (marksOKΣ ms d nt o)

------------------------------------------------------------------------
-- Rule (MARK) alone is preserved: a variable keeps the marks of its
-- entry, and nothing else has a mark.

varMarkΣ : ∀ {Γ t m} → T (varMark Γ m t) → T (varMark (Σctx Γ) m (Σtm t))
varMarkΣ {Γ} {var i} {m} p rewrite marksAtΣ Γ i = p

------------------------------------------------------------------------
-- Suspension preserves scoping (shifting the bound by the two new
-- objects) and local closure. A binder's telescope is left as it is.

mutual
  scΣty : ∀ n A → T (scTy? n A) → T (scTy? (S n) (Σty A))
  scΣty n ⋆           _ = tt
  scΣty n (arr A t u) p =
    let (a , q) = T∧ {scTy? n A} p ; (b , c) = T∧ {scTm? n t} q in
    ∧T (scΣty n A a) (∧T (scΣtm n t b) (scΣtm n u c))

  scΣtm : ∀ n t → T (scTm? n t) → T (scTm? (S n) (Σtm t))
  scΣtm n (var i)       p = p
  scΣtm n (bvar _ _)    _ = tt
  scΣtm n (coh _ _ σ)   p = scΣsub n σ p
  scΣtm n (cst _)       _ = tt
  scΣtm n (bnd _ _ Δ σ) p =
    let (a , b) = T∧ {scTel? n Δ} p in
    ∧T (scTel-suc Δ (scTel-suc Δ a)) (scΣsub n σ b)

  scΣsub : ∀ n σ → T (scSub? n σ) → T (scSub? (S n) (Σsub σ))
  scΣsub n ⟨⟩       _ = tt
  scΣsub n (σ ,ₛ t) p =
    let (a , b) = T∧ {scSub? n σ} p in ∧T (scΣsub n σ a) (scΣtm n t b)

mutual
  lcΣty : ∀ d A → T (lcTy? d A) → T (lcTy? d (Σty A))
  lcΣty d ⋆           _ = tt
  lcΣty d (arr A t u) p =
    let (a , q) = T∧ {lcTy? d A} p ; (b , c) = T∧ {lcTm? d t} q in
    ∧T (lcΣty d A a) (∧T (lcΣtm d t b) (lcΣtm d u c))

  lcΣtm : ∀ d t → T (lcTm? d t) → T (lcTm? d (Σtm t))
  lcΣtm d (var _)       _ = tt
  lcΣtm d (bvar _ _)    p = p
  lcΣtm d (coh _ _ σ)   p = lcΣsub d σ p
  lcΣtm d (cst _)       _ = tt
  lcΣtm d (bnd _ _ Δ σ) p =
    let (a , b) = T∧ {lcTel? (suc d) Δ} p in ∧T a (lcΣsub d σ b)

  lcΣsub : ∀ d σ → T (lcSub? d σ) → T (lcSub? d (Σsub σ))
  lcΣsub d ⟨⟩       _ = tt
  lcΣsub d (σ ,ₛ t) p =
    let (a , b) = T∧ {lcSub? d σ} p in ∧T (lcΣsub d σ a) (lcΣtm d t b)

-- The suspension of an honest arity context is honest.
honestΣ : ∀ G → T (honest? G) → T (honest? (Σctx G))
honestΣ ε             _ = tt
honestΣ (G ▸[ _ ] A) p =
  let (a , q) = T∧ {honest? G} p ; (b , c) = T∧ {scTy? (len G) A} q in
  ∧T (honestΣ G a)
     (∧T (subst (λ n → T (scTy? n (Σty A))) (sym (lenΣ G)) (scΣty (len G) A b))
         (lcΣty 0 A c))
