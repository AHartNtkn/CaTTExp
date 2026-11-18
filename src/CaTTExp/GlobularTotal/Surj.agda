------------------------------------------------------------------------
-- F2c, lemma 2 (second half): every pasting context is built from a
-- tree.
--
--   Γ ⊢ps  ⟹  Σ τ, ctxOf τ ≡ Γ        and so  treeOf Γ ≡ just τ.
--
-- Proof: a zipper (the finished children at each open level) tracks a
-- derivation Γ ⊢ps x ∶ A. pss is the empty zipper, pse opens a level,
-- psd closes one, and building the zipper reproduces (Γ, x, A). At
-- type ⋆ no level is open, so Γ is the context of the root's children.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.GlobularTotal.Surj (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.PastingTrees 𝕊
open import CaTTExp.GlobularTotal.Trees 𝕊 using (treeOf-ctxOf)

State : Set
State = Σ Ctx λ Γ → Σ Nat λ x → Σ Ty λ A → Γ ⊢ps x ∶ A

idx : State → Σ Ctx λ _ → Σ Nat λ _ → Ty
idx (Γ , x , A , _) = Γ , x , A

-- buildList, as a map on states (the type is kept, visibly).
bl : List Tree → State → State
bl ts (Γ , x , A , d) = let r = buildList ts d in fst r , fst (snd r) , A , snd (snd r)

open′ : State → State
open′ (Γ , x , A , d) = _ , _ , _ , pse d

-- buildList over a concatenation is two buildLists.
private
  bl-++ : ∀ ts us {Γ x A} (d : Γ ⊢ps x ∶ A) →
          buildList (ts ++ us) d ≡ (let (Γ′ , x′ , d′) = buildList ts d in buildList us d′)
  bl-++ []             us d = refl
  bl-++ (node cs ∷ ts) us d with build (node cs) (pse d)
  ... | Γ₂ , _ , d₂ = bl-++ ts us (psd d₂)

-- Zippers: the root's finished children, and a stack of open levels
-- (innermost first), each with its finished children.
Zip : Set
Zip = List Tree × List (List Tree)

root : State
root = _ , _ , _ , pss

run : Zip → State
run (F₀ , [])     = bl F₀ root
run (F₀ , F ∷ st) = bl F (open′ (run (F₀ , st)))

depth : Zip → Nat
depth (_ , st) = go st
  where
  go : List (List Tree) → Nat
  go []       = 0
  go (_ ∷ st) = suc (go st)

push : Zip → Zip
push (F₀ , st) = F₀ , [] ∷ st

close : Zip → Zip
close (F₀ , F ∷ [])     = F₀ ++ (node F ∷ []) , []
close (F₀ , F ∷ G ∷ st) = F₀ , (G ++ (node F ∷ [])) ∷ st
close z                 = z

------------------------------------------------------------------------
-- Closing a level is psd.

closeS : State → State
closeS (Γ , f , arr A (var x) (var y) , d) = Γ , y , A , psd d
closeS s = s

bl-close : ∀ G F s → bl (G ++ (node F ∷ [])) s ≡ closeS (bl F (open′ (bl G s)))
bl-close G F (Γ , x , A , d) rewrite bl-++ G (node F ∷ []) d with buildList G d
... | ΓG , xG , dG with build (node F) (pse dG)
...   | Γ₂ , f₂ , d₂ = refl

------------------------------------------------------------------------
-- The invariant.

pseIdx : Σ Ctx (λ _ → Σ Nat (λ _ → Ty)) → Σ Ctx (λ _ → Σ Nat (λ _ → Ty))
pseIdx (Γ , x , A) = Γ ▸ A ▸ arr A (var x) (var (len Γ)) , suc (len Γ) , arr A (var x) (var (len Γ))

psdIdx : Σ Ctx (λ _ → Σ Nat (λ _ → Ty)) → Σ Ctx (λ _ → Σ Nat (λ _ → Ty))
psdIdx (Γ , f , arr A (var x) (var y)) = Γ , y , A
psdIdx i = i

Inv : ∀ {Γ x A} → Γ ⊢ps x ∶ A → Zip → Set
Inv {Γ} {x} {A} d z = (idx (run z) ≡ (Γ , x , A)) × (depth z ≡ dim A)

private
  pred : Nat → Nat
  pred zero    = zero
  pred (suc n) = n

  0≢suc : ∀ {n} → zero ≡ suc n → ⊥
  0≢suc ()

zip-of : ∀ {Γ x A} (d : Γ ⊢ps x ∶ A) → Σ Zip (Inv d)
zip-of pss = ([] , []) , refl , refl
zip-of (pse d) with zip-of d
... | z , e , dp = push z , cong pseIdx e , cong suc dp
zip-of (psd d) with zip-of d
... | (F₀ , [])          , e , dp = ⊥-elim (0≢suc dp)
... | (F₀ , F ∷ [])      , e , dp =
  (F₀ ++ (node F ∷ []) , []) ,
  trans (cong idx (bl-close F₀ F root)) (cong psdIdx e) ,
  cong pred dp
... | (F₀ , F ∷ G ∷ st)  , e , dp =
  (F₀ , (G ++ (node F ∷ [])) ∷ st) ,
  trans (cong idx (bl-close G F (open′ (run (F₀ , st))))) (cong psdIdx e) ,
  cong pred dp

------------------------------------------------------------------------
-- Every pasting context is the context of a tree.

ctxOf-node : ∀ ts → ctxOf (node ts) ≡ fst (buildList ts pss)
ctxOf-node ts with build (node ts) pss
... | Γ , _ , d = refl

surj : ∀ {Γ} → Γ ⊢ps → Σ Tree (λ τ → ctxOf τ ≡ Γ)
surj (ps d) with zip-of d
... | (F₀ , [])     , e , dp = node F₀ , trans (ctxOf-node F₀) (cong fst e)
... | (F₀ , _ ∷ _)  , e , ()

-- So treeOf succeeds on every pasting context, and inverts ctxOf.
treeOf-ps : ∀ {Γ} → Γ ⊢ps → Σ Tree (λ τ → (treeOf Γ ≡ just τ) × (ctxOf τ ≡ Γ))
treeOf-ps p with surj p
... | τ , eq = τ , subst (λ Δ → treeOf Δ ≡ just τ) eq (treeOf-ctxOf τ) , eq
