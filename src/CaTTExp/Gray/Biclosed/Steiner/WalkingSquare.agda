------------------------------------------------------------------------
-- The walking square in 𝒮 (D7g examples): no reverse interchanger.
--
-- K = λD¹ ⊗ λD¹.  A 2-cell is a map m : λD² → K; its faces are the
-- restrictions along δ^± (`face`).  The chain condition of m at the
-- 1-cell n₀ = (t, top) reads
--   m(top)(top,top) + (source face)(n₀) = (target face)(n₀)
-- (`square-eq`), so no 2-cell has n₀ in its source face and not in its
-- target (`no-reverse-face`): the path through n₀ never maps to the
-- other one.  This is Strict/ReverseInterchanger redone in the codes
-- of the 𝔖̂ instance.  No postulates.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.WalkingSquare (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Globe
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (globe; Code)
open import CaTTExp.Gray.Biclosed.Steiner.Maps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.GlobeMaps nmFB using (δmap)

K : Code
K = globe 1 ∷ globe 1 ∷ []

pickʳ : ∀ {L} (f : El L → Nat) (b : El L → Nat) l₀ → (∀ l → b l ≡ δE L l l₀) → Σl (els′ L) (λ l → f l * b l) ≡ f l₀
pickʳ {L} f b l₀ P = trans (Σ-cong (els′ L) (λ l → cong (f l *_) (P l))) (Σ-δʳ (enumEl L) l₀ f)

pickˡ : ∀ {L} (f : El L → Nat) (b : El L → Nat) l₀ → (∀ l → b l ≡ δE L l₀ l) → Σl (els′ L) (λ l → b l * f l) ≡ f l₀
pickˡ {L} f b l₀ P = trans (Σ-cong (els′ L) (λ l → cong (_* f l) (P l))) (Σ-δ (enumEl L) l₀ f)

tt₂ : El (D 2)
tt₂ = top , tt

n₀ : El K
n₀ = tgt fz , (top , tt)

PK : ∀ l → bd K true l n₀ ≡ δE K l (top , (top , tt))
PK (top , top , tt) = refl
PK (top , src fz , tt) = refl
PK (top , tgt fz , tt) = refl
PK (src fz , top , tt) = refl
PK (src fz , src fz , tt) = refl
PK (src fz , tgt fz , tt) = refl
PK (tgt fz , top , tt) = refl
PK (tgt fz , src fz , tt) = refl
PK (tgt fz , tgt fz , tt) = refl
PK (src (fs ()) , _)
PK (tgt (fs ()) , _)
PK (_ , src (fs ()) , _)
PK (_ , tgt (fs ()) , _)

PK⁻ : ∀ l → bd K false l n₀ ≡ 0
PK⁻ (top , top , tt) = refl
PK⁻ (top , src fz , tt) = refl
PK⁻ (top , tgt fz , tt) = refl
PK⁻ (src fz , top , tt) = refl
PK⁻ (src fz , src fz , tt) = refl
PK⁻ (src fz , tgt fz , tt) = refl
PK⁻ (tgt fz , top , tt) = refl
PK⁻ (tgt fz , src fz , tt) = refl
PK⁻ (tgt fz , tgt fz , tt) = refl
PK⁻ (src (fs ()) , _)
PK⁻ (tgt (fs ()) , _)
PK⁻ (_ , src (fs ()) , _)
PK⁻ (_ , tgt (fs ()) , _)

s₂ t₂ : El (D 2)
s₂ = src (fs fz) , tt
t₂ = tgt (fs fz) , tt

PD : ∀ α j → bd (D 2) α tt₂ j ≡ δE (D 2) (if α then t₂ else s₂) j
PD true (top , tt) = refl
PD false (top , tt) = refl
PD true (src fz , tt) = refl
PD true (src (fs fz) , tt) = refl
PD true (tgt fz , tt) = refl
PD true (tgt (fs fz) , tt) = refl
PD false (src fz , tt) = refl
PD false (src (fs fz) , tt) = refl
PD false (tgt fz , tt) = refl
PD false (tgt (fs fz) , tt) = refl
PD _ (src (fs (fs ())) , tt)
PD _ (tgt (fs (fs ())) , tt)

Σ-zero : ∀ {A : Set} (xs : List A) (f g : A → Nat) → (∀ x → g x ≡ 0) → Σl xs (λ x → f x * g x) ≡ 0
Σ-zero []       f g e = refl
Σ-zero (x ∷ xs) f g e = cong₂ _+_ (trans (cong (f x *_) (e x)) (*-zero (f x))) (Σ-zero xs f g e)

-- In a 2-cell m : λD² → λD¹ ⊗ λD¹, the target face has at least as many
-- copies of n₀ = t ⊗ top as the source face, plus the top coefficient.
square-eq : ∀ (m : Map (D 2) K) →
            mat m tt₂ (top , (top , tt)) + mat m s₂ n₀ ≡ mat m t₂ n₀
square-eq m =
  trans (sym (cong₂ _+_ (pickʳ {K} (mat m tt₂) (λ l → bd K true l n₀) _ PK)
                        (pickˡ {D 2} (λ j → mat m j n₀) (bd (D 2) false tt₂) s₂ (PD false))))
  (trans (mchain m tt₂ n₀)
         (cong₂ _+_ (Σ-zero (els′ K) (mat m tt₂) (λ l → bd K false l n₀) PK⁻)
                    (pickˡ {D 2} (λ j → mat m j n₀) (bd (D 2) true tt₂) t₂ (PD true))))

-- So no 2-cell has n₀ in its source face and not in its target face:
-- the reverse interchanger has no cell.
no-reverse-square : ∀ (m : Map (D 2) K) a → mat m s₂ n₀ ≡ suc a → mat m t₂ n₀ ≡ 0 → ⊥
no-reverse-square m a es et with trans (square-eq m) et
... | e rewrite es | +-suc (mat m tt₂ (top , (top , tt))) a = suc≢0 e
  where suc≢0 : ∀ {k} → suc k ≡ 0 → ⊥
        suc≢0 ()

-- the faces of a 2-cell are its restrictions along δ^±
Pδ : ∀ α j → mat (δmap α 1) (top , tt) j ≡ δE (D 2) (if α then t₂ else s₂) j
Pδ true (top , tt) = refl
Pδ false (top , tt) = refl
Pδ true (src fz , tt) = refl
Pδ true (src (fs fz) , tt) = refl
Pδ true (tgt fz , tt) = refl
Pδ true (tgt (fs fz) , tt) = refl
Pδ false (src fz , tt) = refl
Pδ false (src (fs fz) , tt) = refl
Pδ false (tgt fz , tt) = refl
Pδ false (tgt (fs fz) , tt) = refl
Pδ _ (src (fs (fs ())) , tt)
Pδ _ (tgt (fs (fs ())) , tt)

face : ∀ α (m : Map (D 2) K) n → mat (m ∘M δmap α 1) (top , tt) n ≡ mat m (if α then t₂ else s₂) n
face α m n = pickˡ {D 2} (λ j → mat m j n) _ _ (Pδ α)

-- The walking square λD¹ ⊗ λD¹ has two paths from (s,s) to (t,t):
-- P₋ = (top,s);(t,top) through n₀ = (t,top), and P₊ = (s,top);(top,t).
-- A 2-cell with source face through n₀ must have its target through n₀
-- too, so there is no 2-cell P₋ ⇒ P₊.  (P₊ ⇒ P₋ is the interchanger.)
no-reverse-face : ∀ (m : Map (D 2) K) a →
                  mat (m ∘M δmap false 1) (top , tt) n₀ ≡ suc a →
                  mat (m ∘M δmap true 1) (top , tt) n₀ ≡ 0 → ⊥
no-reverse-face m a es et =
  no-reverse-square m a (trans (sym (face false m n₀)) es) (trans (sym (face true m n₀)) et)
