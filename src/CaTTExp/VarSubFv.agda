------------------------------------------------------------------------
-- Free variables under variable substitutions.
--
-- A variable substitution σ (every entry a variable) acts on levels by
-- `lev ∘ lookupₛ σ`. Every free variable w of t is sent to a free
-- variable of t[σ] (`fv-tm-mem`, and the same for types and
-- substitutions). So if t uses every level below n, then t[σ] uses
-- every level in the image of σ on them (`full-img`).
------------------------------------------------------------------------
module CaTTExp.VarSubFv where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (Mem; mem++; mem++l; mem++r; mem-one; ∨-l; _⊎_; inj₁; inj₂)

lev : Tm → Nat
lev (var i) = i
lev _       = 0

IsVar : Tm → Set
IsVar (var _) = ⊤
IsVar _       = ⊥

VarSub : Sub → Set
VarSub ⟨⟩       = ⊤
VarSub (σ ,ₛ t) = VarSub σ × IsVar t

private
  isVar-eq : ∀ t → IsVar t → t ≡ var (lev t)
  isVar-eq (var i) _ = refl

  mem-self : ∀ u → u ≡ var (lev u) → Mem (lev u) (fvTm u)
  mem-self (var j) _ = ∨-l (==ℕ-refl j)

-- Every lookup in a variable substitution is a variable (out of range
-- too, where lookupₛ returns var i).
lk-var : ∀ σ i → VarSub σ → lookupₛ σ i ≡ var (lev (lookupₛ σ i))
lk-var ⟨⟩       i _       = refl
lk-var (σ ,ₛ t) i (v , w) with i ==ℕ lenₛ σ
... | true  = isVar-eq t w
... | false = lk-var σ i v

mutual
  fv-ty-mem : ∀ A σ w → VarSub σ → Mem w (fvTy A) → Mem (lev (lookupₛ σ w)) (fvTy (A [ σ ]ty))
  fv-ty-mem ⋆           σ w v ()
  fv-ty-mem (arr A t u) σ w v m with mem++ w (fvTy A) _ m
  ... | inj₁ r = mem++l _ (fvTy (A [ σ ]ty)) _ (fv-ty-mem A σ w v r)
  ... | inj₂ r with mem++ w (fvTm t) _ r
  ...   | inj₁ s = mem++r _ (fvTy (A [ σ ]ty)) _ (mem++l _ (fvTm (t [ σ ]tm)) _ (fv-tm-mem t σ w v s))
  ...   | inj₂ s = mem++r _ (fvTy (A [ σ ]ty)) _ (mem++r _ (fvTm (t [ σ ]tm)) _ (fv-tm-mem u σ w v s))

  fv-tm-mem : ∀ t σ w → VarSub σ → Mem w (fvTm t) → Mem (lev (lookupₛ σ w)) (fvTm (t [ σ ]tm))
  fv-tm-mem (var i)     σ w v m =
    subst (λ x → Mem (lev (lookupₛ σ x)) (fvTm (lookupₛ σ i))) (sym (mem-one w i m))
      (mem-self (lookupₛ σ i) (lk-var σ i v))
  fv-tm-mem (coh Δ A ρ) σ w v m = fv-sub-mem ρ σ w v m
  fv-tm-mem (cst _)     σ w v ()

  fv-sub-mem : ∀ ρ σ w → VarSub σ → Mem w (fvSub ρ) → Mem (lev (lookupₛ σ w)) (fvSub (ρ ∘ σ))
  fv-sub-mem ⟨⟩       σ w v ()
  fv-sub-mem (ρ ,ₛ t) σ w v m with mem++ w (fvSub ρ) (fvTm t) m
  ... | inj₁ r = mem++l _ (fvSub (ρ ∘ σ)) _ (fv-sub-mem ρ σ w v r)
  ... | inj₂ r = mem++r _ (fvSub (ρ ∘ σ)) _ (fv-tm-mem t σ w v r)

-- A term using every level below n: its image uses the image of each.
Full : Nat → List Nat → Set
Full n xs = ∀ w → T (w <ℕ n) → Mem w xs

full-img : ∀ t σ n → VarSub σ → Full n (fvTm t) →
           ∀ w → T (w <ℕ n) → Mem (lev (lookupₛ σ w)) (fvTm (t [ σ ]tm))
full-img t σ n v f w p = fv-tm-mem t σ w v (f w p)
