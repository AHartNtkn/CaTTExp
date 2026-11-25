------------------------------------------------------------------------
-- Coherence mark rules given as clauses with positive bodies
-- (notes/unified-engine.md §3.3).
--
-- A clause concludes one mark `concl` for coh Δ A τ when a when on
-- the head (Δ, A) holds and a positive Boolean formula over atoms
-- "argument i has mark m" holds of the pulled-back marking. Every
-- propagation rule of spec chapter 3 has this shape:
--   (COH-inv)    when: coherence case;  body: true
--   (OP-inv)     when: operation case;  body: ⋀ over top generators g, "g[γ] inv"
--   (INV-fac)    when: Gray cell;       body: ⋁ over factors i with dᵢ ≥ 1, "xᵢ inv"
--   (ORD)        when: inner coherence; body: "aₙ ord" (or iord)
--   (INN-fac_S)  when: inner interchanger; body: (lsplit ∧ left inv) ∨ (rsplit ∧ right inv)
-- and so on. A positive body is monotone in the marking, so every
-- clause list satisfies the hypotheses of CaTTExp.Binder.FreeModelMark
-- and inherits renaming, substitution and the kernel's checker. The
-- theorem is about the form of the rules, not about which clauses are
-- sound: soundness of each clause is a separate (semantic) statement.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM

module CaTTExp.Binder.FreeModelMarkPos
  (𝕊 : Signature)
  (_⊑_ : BM.Mark → BM.Mark → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas K B using (T∧; ∧T)

-- Positive formulas over atoms "argument i has mark m".
data Pos : Set where
  yes  : Pos
  atom : Nat → Mark → Pos
  _∧ᵖ_ _∨ᵖ_ : Pos → Pos → Pos

evalP : (Nat → Mark → Bool) → Pos → Bool
evalP f yes        = true
evalP f (atom i m) = f i m
evalP f (p ∧ᵖ q)   = evalP f p ∧ evalP f q
evalP f (p ∨ᵖ q)   = evalP f p ∨ evalP f q

allP : List Pos → Pos
allP []       = yes
allP (p ∷ ps) = p ∧ᵖ allP ps

record Clause : Set where
  field
    concl : Mark
    when : Ctx → Ty → Bool
    body  : Ctx → Ty → Pos
open Clause public

anyC : (Clause → Bool) → List Clause → Bool
anyC p []       = false
anyC p (c ∷ cs) = p c ∨ anyC p cs

-- The oracle a clause list defines.
cohHasC : List Clause → Ctx → Ty → (Nat → Mark → Bool) → Mark → Bool
cohHasC cs Δ A f m =
  anyC (λ c → (concl c ⊑ m) ∧ when c Δ A ∧ evalP f (body c Δ A)) cs

private
  T∨ˡ : ∀ {a} b → T a → T (a ∨ b)
  T∨ˡ {true} b _ = tt

  T∨ʳ : ∀ a {b} → T b → T (a ∨ b)
  T∨ʳ true  _ = tt
  T∨ʳ false p = p

  anyC-mono : ∀ (p q : Clause → Bool) cs → (∀ c → T (p c) → T (q c)) →
              T (anyC p cs) → T (anyC q cs)
  anyC-mono p q (c ∷ cs) f r with p c in e
  ... | true  = T∨ˡ (anyC q cs) (f c (subst T (sym e) tt))
  ... | false = T∨ʳ (q c) (anyC-mono p q cs f r)

-- Positive formulas are monotone in the marking.
evalP-mono : ∀ {f g} → (∀ i m → T (f i m) → T (g i m)) → ∀ p →
             T (evalP f p) → T (evalP g p)
evalP-mono h yes        _ = tt
evalP-mono h (atom i m) r = h i m r
evalP-mono {f} {g} h (p ∧ᵖ q) r =
  let (a , b) = T∧ {evalP f p} r in ∧T (evalP-mono h p a) (evalP-mono h q b)
evalP-mono {f} {g} h (p ∨ᵖ q) r with evalP f p in e
... | true  = T∨ˡ (evalP g q) (evalP-mono h p (subst T (sym e) tt))
... | false = T∨ʳ (evalP g p) (evalP-mono h q r)

module _ (⊑-trans : ∀ {l m n} → T (l ⊑ m) → T (m ⊑ n) → T (l ⊑ n)) (cs : List Clause) where

  cohC-mono : ∀ {Δ A f g m} → (∀ i m → T (f i m) → T (g i m)) →
              T (cohHasC cs Δ A f m) → T (cohHasC cs Δ A g m)
  cohC-mono {Δ} {A} {f} {g} {m} h =
    anyC-mono _ _ cs λ c r →
      let (a , s) = T∧ {concl c ⊑ m} r ; (b , d) = T∧ {when c Δ A} s in
      ∧T a (∧T b (evalP-mono h (body c Δ A) d))

  cohC-up : ∀ {Δ A f m n} → T (cohHasC cs Δ A f m) → T (m ⊑ n) → T (cohHasC cs Δ A f n)
  cohC-up {Δ} {A} {f} {m} {n} r q =
    anyC-mono _ _ cs (λ c s → let (a , t) = T∧ {concl c ⊑ m} s in ∧T (⊑-trans a q) t) r
