------------------------------------------------------------------------
-- The presupposition law (CaTTExp.Binder.Presup, `PresupLaws`) for the
-- Gray object formers with the unary-multimap heads
-- (CaTTExp.Binder.Multimap), over any binder-free 𝕊₀, every coh side
-- condition and every mark judgment.
--
-- For an mm head whose side condition holds, with k atoms and Φ's
-- entries (X_j ▸ Z_j): opened after Γ (|Γ| = g), the arity is
--   Γ, a₀ … a_{k-1} : ⋆, f_j : ⟦X_j⟧ → ⟦Z_j⟧
-- with atom i read as var (g + i), and it is a well-formed context
-- (each ⟦X⟧ is an object, typed by (GB-form)); the opened type
-- ⟦X⟧ → ⟦Z⟧ is well formed in it. The side condition guarantees that
-- every formula involved is an atom formula below k (`mmTy-ok`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.GrayForm
open import CaTTExp.Binder.Multimap
import CaTTExp.Binder.Mark as BM
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT

module CaTTExp.Binder.MultimapPresup (𝕊₀ : Old.Signature) where

open import CaTTExp.Binder.MultimapLaws 𝕊₀ using (𝕊; sc-fmB)
open Signature 𝕊
open GMInterface K
open import CaTTExp.Binder.SyntaxLemmas K B

------------------------------------------------------------------------
-- Arithmetic.

==-+ : ∀ g i k → (g + i ==ℕ g + k) ≡ (i ==ℕ k)
==-+ zero    i k = refl
==-+ (suc g) i k = ==-+ g i k

<-+ᴸ : ∀ g i k → T (i <ℕ k) → T (g + i <ℕ g + k)
<-+ᴸ zero    i k p = p
<-+ᴸ (suc g) i k p = <-+ᴸ g i k p

------------------------------------------------------------------------
-- Inversion of the side condition.

AllAtom : Nat → List (GB.Fm × GB.Fm) → Set
AllAtom k []             = ⊤
AllAtom k ((x , z) ∷ ps) = T (atomFm k x) × T (atomFm k z) × AllAtom k ps

bind-just : ∀ {A C : Set} (m : Maybe A) (f : A → Maybe C) {c} →
            (m >>= f) ≡ just c → Σ A λ a → (m ≡ just a) × (f a ≡ just c)
bind-just (just a) f e = a , refl , e
bind-just nothing  f ()

unaryTy-ok : ∀ k A {x z} → unaryTy k A ≡ just (x , z) → T (atomFm k x) × T (atomFm k z)
unaryTy-ok k (GB.op ((x ∷ []) GB.▸ z)) e with atomFm k x in ex | atomFm k z in ez
unaryTy-ok k (GB.op ((x ∷ []) GB.▸ z)) refl | true | true = ≡→T ex , ≡→T ez
unaryTy-ok k (GB.op ((x ∷ []) GB.▸ z)) () | true | false
unaryTy-ok k (GB.op ((x ∷ []) GB.▸ z)) () | false | _
unaryTy-ok k (GB.op ([] GB.▸ _)) ()
unaryTy-ok k (GB.op ((_ ∷ _ ∷ _) GB.▸ _)) ()
unaryTy-ok k (GB.hom _ _ _ _ _) ()

allUnary-ok : ∀ k Φ {ps} → allUnary k Φ ≡ just ps → AllAtom k ps
allUnary-ok k [] refl = tt
allUnary-ok k (A ∷ As) e with bind-just (unaryTy k A) _ e
... | (x , z) , e₁ , e₂ with bind-just (allUnary k As) _ e₂
... | ps , e₃ , refl =
  let (ax , az) = unaryTy-ok k A e₁ in ax , az , allUnary-ok k As e₃

mmTy-ok : ∀ b {ps x z} → mmTy b ≡ just (ps , (x , z)) →
          AllAtom (atoms b) ps × T (atomFm (atoms b) x) × T (atomFm (atoms b) z)
mmTy-ok (mmi k Φ t) e with bind-just (allUnary k Φ) _ e
... | ps , e₁ , e₂ with bind-just (((if GT.wfCtx Φ ∧ all (sortedY k) Φ ∧ sortedT k t then GT.infer Φ t else nothing)) >>= unaryTy k) _ e₂
... | xz , e₃ , refl with bind-just (if GT.wfCtx Φ ∧ all (sortedY k) Φ ∧ sortedT k t then GT.infer Φ t else nothing) (unaryTy k) e₃
... | A , _ , e₄ = allUnary-ok k Φ e₁ , unaryTy-ok k A e₄

------------------------------------------------------------------------
-- Opening formulas.

fmV : Nat → GB.Fm → Tm
fmV g = fmWith (λ i → var (g + i))

pick-fresh : ∀ g n i d → T (i <ℕ n) → pickOr (fresh g n) i d ≡ var (g + i)
pick-fresh g (suc n) i d p rewrite lenₛ-fresh g n with i ==ℕ n in e
... | true  = cong (λ x → var (g + x)) (sym (==→≡ i n e))
... | false = pick-fresh g n i d (<suc-≢ i n p e)

op-fmB : ∀ g n k x → (∀ i → T (i <ℕ k) → T (i <ℕ n)) → T (atomFm k x) →
         opTm 0 (fresh g n) (fmB x) ≡ fmV g x
op-fmB g n k (GB.obj i)  h p = pick-fresh g n i (bvar 0 i) (h i p)
op-fmB g n k (GB.rep _)  h ()
op-fmB g n k (GB.shp _)  h ()
op-fmB g n k (x GB.⊗ y)  h p rewrite op-fmB g n k x h (∧-fst p) | op-fmB g n k y h (∧-snd {atomFm k x} p) = refl
op-fmB g n k (x GB.\\ y) h p rewrite op-fmB g n k x h (∧-fst p) | op-fmB g n k y h (∧-snd {atomFm k x} p) = refl
op-fmB g n k (x GB.// y) h p rewrite op-fmB g n k x h (∧-fst p) | op-fmB g n k y h (∧-snd {atomFm k x} p) = refl

------------------------------------------------------------------------
-- Closedness of the arity (for bargs-sc).

sc-atomsTel : ∀ n k → T (scTel? n (atomsTel k))
sc-atomsTel n zero    = tt
sc-atomsTel n (suc k) = ∧T (sc-atomsTel n k) tt

sc-cellsTel : ∀ n Θ ps → T (scTel? n Θ) → T (scTel? n (cellsTel Θ ps))
sc-cellsTel n Θ []             p = p
sc-cellsTel n Θ ((x , z) ∷ ps) p =
  sc-cellsTel n _ ps (∧T p (subst T (sym (cong₂ _∧_ (sc-fmB n x) (sc-fmB n z))) tt))

sc-argsM : ∀ b y Δ n → T (scTel? n (argsM b y Δ))
sc-argsM b y Δ n with mmTy b
... | just (ps , _) = sc-cellsTel n _ ps (sc-atomsTel n (atoms b))
... | nothing       = tt

------------------------------------------------------------------------
-- Typing.

module _ (side′ : Ctx → Ty → Tm → Tm → Bool) (mark : Ctx → BM.Mark → Tm → Bool) where

  open import CaTTExp.Binder.TypingWith 𝕊 side′ mark
  open import CaTTExp.Binder.Presup 𝕊 side′ mark using (PresupLaws; tm-ctx)

  -- Positions g, …, g + k − 1 of Θ hold objects.
  AtomsAt : Ctx → Nat → Nat → Set
  AtomsAt Θ g k = ∀ i → T (i <ℕ k) → lookup Θ (g + i) ≡ just ⋆

  gbT : ∀ {Θ a c} kd → Θ ⊢tm a ∶ ⋆ → Θ ⊢tm c ∶ ⋆ → Θ ⊢tm gbApp kd a c ∶ ⋆
  gbT kd da dc = bnd-wf tt tt w tt (,-a (,-a (⟨⟩-a w) da tt) dc tt)
    where w = tm-ctx da

  fm-ty : ∀ {Θ g k} → Θ ⊢ctx → AtomsAt Θ g k → ∀ x → T (atomFm k x) → Θ ⊢tm fmV g x ∶ ⋆
  fm-ty w at (GB.obj i)  p = var-wf w (at i p)
  fm-ty w at (GB.rep _)  ()
  fm-ty w at (GB.shp _)  ()
  fm-ty {k = k} w at (x GB.⊗ y)  p = gbT tensorK (fm-ty w at x (∧-fst p)) (fm-ty w at y (∧-snd {atomFm k x} p))
  fm-ty {k = k} w at (x GB.\\ y) p = gbT lhomK   (fm-ty w at x (∧-fst p)) (fm-ty w at y (∧-snd {atomFm k x} p))
  fm-ty {k = k} w at (x GB.// y) p = gbT rhomK   (fm-ty w at x (∧-fst p)) (fm-ty w at y (∧-snd {atomFm k x} p))

  -- Extending a context keeps the atoms in place.
  atoms-ext : ∀ {Θ g k ms A} → (∀ i → T (i <ℕ k) → T (g + i <ℕ len Θ)) →
              AtomsAt Θ g k → AtomsAt (Θ ▸[ ms ] A) g k
  atoms-ext {Θ} {g} lt at i p rewrite <→≢ (g + i) (len Θ) (lt i p) = at i p

  -- The opened atoms.
  len-atoms : ∀ Γ k → len (Γ ⧺ openTel (len Γ) (atomsTel k)) ≡ len Γ + k
  len-atoms Γ k = trans (len-⧺ Γ (openTel (len Γ) (atomsTel k)))
                        (cong (len Γ +_) (trans (len-openTel (len Γ) (atomsTel k)) (len-atomsTel k)))
    where
    len-atomsTel : ∀ k → len (atomsTel k) ≡ k
    len-atomsTel zero    = refl
    len-atomsTel (suc k) = cong suc (len-atomsTel k)

  atoms-wf : ∀ {Γ} k → Γ ⊢ctx → (Γ ⧺ openTel (len Γ) (atomsTel k)) ⊢ctx
  atoms-wf zero    w = w
  atoms-wf (suc k) w = ▸-wf (atoms-wf k w) (⋆-wf (atoms-wf k w))

  atoms-at : ∀ Γ k → AtomsAt (Γ ⧺ openTel (len Γ) (atomsTel k)) (len Γ) k
  atoms-at Γ (suc k) i p
    rewrite len-atoms Γ k | ==-+ (len Γ) i k with i ==ℕ k in e
  ... | true  = refl
  ... | false = atoms-at Γ k i (<suc-≢ i k p e)

  -- The opened cells, over any prefix Θ of the arity that contains the
  -- atoms.
  record Prefix (Γ Θ : Ctx) (k : Nat) : Set where
    field
      wf  : (Γ ⧺ openTel (len Γ) Θ) ⊢ctx
      at  : AtomsAt (Γ ⧺ openTel (len Γ) Θ) (len Γ) k
      big : ∀ i → T (i <ℕ k) → T (i <ℕ len Θ)

  len-pre : ∀ Γ Θ → len (Γ ⧺ openTel (len Γ) Θ) ≡ len Γ + len Θ
  len-pre Γ Θ = trans (len-⧺ Γ _) (cong (len Γ +_) (len-openTel (len Γ) Θ))

  cells-ok : ∀ {Γ k} Θ ps → AllAtom k ps → Prefix Γ Θ k → Prefix Γ (cellsTel Θ ps) k
  cells-ok Θ [] _ P = P
  cells-ok {Γ} {k} Θ ((x , z) ∷ ps) (ax , az , rest) P =
    cells-ok (Θ ▸ arr ⋆ (fmB x) (fmB z)) ps rest record
      { wf  = ▸-wf (Prefix.wf P) cellTy
      ; at  = atoms-ext {Θ = Γ ⧺ openTel (len Γ) Θ} {g = len Γ} {k = k} {ms = []} {A = opTy 0 (fresh (len Γ) (len Θ)) (arr ⋆ (fmB x) (fmB z))} lt (Prefix.at P)
      ; big = λ i p → <-suc i (len Θ) (Prefix.big P i p) }
    where
    g = len Γ
    lt : ∀ i → T (i <ℕ k) → T (g + i <ℕ len (Γ ⧺ openTel g Θ))
    lt i p rewrite len-pre Γ Θ = <-+ᴸ g i (len Θ) (Prefix.big P i p)
    cellTy : (Γ ⧺ openTel g Θ) ⊢ty opTy 0 (fresh g (len Θ)) (arr ⋆ (fmB x) (fmB z))
    cellTy rewrite op-fmB g (len Θ) k x (Prefix.big P) ax | op-fmB g (len Θ) k z (Prefix.big P) az =
      arr-wf (fm-ty (Prefix.wf P) (Prefix.at P) x ax) (fm-ty (Prefix.wf P) (Prefix.at P) z az)

  atoms-prefix : ∀ {Γ} k → Γ ⊢ctx → Prefix Γ (atomsTel k) k
  atoms-prefix {Γ} k w = record
    { wf = atoms-wf k w ; at = atoms-at Γ k ; big = λ i p → subst (λ n → T (i <ℕ n)) (sym (len-at k)) p }
    where
    len-at : ∀ k → len (atomsTel k) ≡ k
    len-at zero    = refl
    len-at (suc k) = cong suc (len-at k)

  ----------------------------------------------------------------------
  -- res-wf.

  isε-T : ∀ Δ → T (isε Δ) → Δ ≡ ε
  isε-T ε _ = refl
  isε-T (_ ▸[ _ ] _) ()

  res-wfM : ∀ {Γ} b y Δ → (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (sideM b y Δ) →
            (Γ ⧺ openTel (len Γ) (argsM b y Δ)) ⊢ty
              opTy 0 (fresh (len Γ) (len (argsM b y Δ))) (resM b y Δ)
  res-wfM {Γ} b y Δ w p with isε-T Δ (∧-fst (∧-snd {y ==ℕ 0} p))
  ... | refl with mmTy b in e
  ... | just (ps , (x , z)) =
    let (aps , ax , az) = mmTy-ok b e
        P = cells-ok (atomsTel (atoms b)) ps aps (atoms-prefix (atoms b) w)
        n = len (cellsTel (atomsTel (atoms b)) ps)
    in subst₂ (Γ ⧺ openTel (len Γ) (cellsTel (atomsTel (atoms b)) ps) ⊢ty_)
         (sym (op-fmB (len Γ) n (atoms b) x (Prefix.big P) ax))
         (sym (op-fmB (len Γ) n (atoms b) z (Prefix.big P) az))
         (arr-wf (fm-ty (Prefix.wf P) (Prefix.at P) x ax) (fm-ty (Prefix.wf P) (Prefix.at P) z az))
    where
    subst₂ : ∀ (P′ : Ty → Set) {a a′ c c′ : Tm} → a ≡ a′ → c ≡ c′ →
             P′ (arr ⋆ a c) → P′ (arr ⋆ a′ c′)
    subst₂ P′ refl refl d = d
  res-wfM {Γ} b y Δ w p | refl | nothing = ⊥-elim (∧-snd {isε ε} (∧-snd {y ==ℕ 0} p))

  ----------------------------------------------------------------------
  -- The law, former by former.

  res-wfGF : ∀ {Γ} b y Δ → (Γ ⧺ openTel (len Γ) Δ) ⊢ctx → T (side b y Δ) →
             (Γ ⧺ openTel (len Γ) (args b y Δ)) ⊢ty
               opTy 0 (fresh (len Γ) (len (args b y Δ))) (res b y Δ)
  res-wfGF b y Δ w p with isε-T Δ (∧-snd {y ==ℕ 0} p)
  ... | refl = ⋆-wf (▸-wf (▸-wf w (⋆-wf w)) (⋆-wf (▸-wf w (⋆-wf w))))

  gmPresup : PresupLaws
  gmPresup = record
    { bargs-sc = λ { (gform b) y Δ n _ _ → tt
                   ; (mmh b)   y Δ n _ _ → sc-argsM b y Δ n }
    ; res-wf   = λ { {b = gform b} {y} {Δ} _ _ w p → res-wfGF b y Δ w p
                   ; {b = mmh b}   {y} {Δ} _ _ w p → res-wfM b y Δ w p }
    }
