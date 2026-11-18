------------------------------------------------------------------------
-- F2c, the variable case of (1′): the globe of a variable.
--
-- For x : A in Γ with A's endpoints variables of Γ (PsOrd.TyIn), the
-- normal form of x is `wrapT A (lt (x ∷ []) [])`, and it is
--   * well formed, of dimension dim A,           (wrapT-wf, wrapT-dim)
--   * a diagram of Γ,                             (wrapT-ex)
--   * with dim B boundaries the globes of A's endpoints (wrapT-bd),
--   * labelled by x and the variables of A.      (wrapT-mem)
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.Wrap where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; wrap; bd; bdL)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL; AllN; Cell; Ex; ExCs; dimOf)
open import CaTTExp.GlobularTotal.PsOrd using (TyIn)
open import CaTTExp.GlobularTotal.LabEx using (parOf)

private
  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  ∨-assoc : ∀ a b c → ((a ∨ b) ∨ c) ≡ (a ∨ (b ∨ c))
  ∨-assoc true  b c = refl
  ∨-assoc false b c = refl

-- The globe of a cell of type A around the tree s (total; agrees with
-- wrap on types whose endpoints are variables).
wrapT : Ty → LT → LT
wrapT ⋆                       s = s
wrapT (arr B (var a) (var b)) s = wrapT B (lt (a ∷ b ∷ []) (s ∷ []))
wrapT (arr B _ _)             s = s

wrap-T : ∀ Γ A s → TyIn Γ A → wrap A s ≡ just (wrapT A s)
wrap-T Γ ⋆                       s _ = refl
wrap-T Γ (arr B (var a) (var b)) s (_ , _ , _ , _ , t) = wrap-T Γ B _ t
wrap-T Γ (arr B (var a) (coh _ _ _)) s ()
wrap-T Γ (arr B (var a) (cst ()))    s _
wrap-T Γ (arr B (coh _ _ _) _)       s ()
wrap-T Γ (arr B (cst ()) _)          s _

wrapT-wf : ∀ Γ A s → TyIn Γ A → WF s → WF (wrapT A s)
wrapT-wf Γ ⋆                       s _ w = w
wrapT-wf Γ (arr B (var a) (var b)) s (_ , _ , _ , _ , t) w = wrapT-wf Γ B _ t (refl , (w , tt))
wrapT-wf Γ (arr B (var a) (coh _ _ _)) s ()
wrapT-wf Γ (arr B (var a) (cst ()))    s _
wrapT-wf Γ (arr B (coh _ _ _) _)       s ()
wrapT-wf Γ (arr B (cst ()) _)          s _

-- Boundaries above the wrapping go inside it.
wrapT-bd : ∀ Γ A s β k → TyIn Γ A → bd β (dim A + k) (wrapT A s) ≡ wrapT A (bd β k s)
wrapT-bd Γ ⋆                       s β k _ = refl
wrapT-bd Γ (arr B (var a) (var b)) s β k (_ , _ , _ , _ , t)
  rewrite sym (+-suc (dim B) k) = trans (wrapT-bd Γ B _ β (suc k) t) (cong (wrapT B) (bd-suc β))
  where
  bd-suc : ∀ β → bd β (suc k) (lt (a ∷ b ∷ []) (s ∷ [])) ≡ lt (a ∷ b ∷ []) (bd β k s ∷ [])
  bd-suc false = refl
  bd-suc true  = refl
wrapT-bd Γ (arr B (var a) (coh _ _ _)) s β k ()
wrapT-bd Γ (arr B (var a) (cst ()))    s β k _
wrapT-bd Γ (arr B (coh _ _ _) _)       s β k ()
wrapT-bd Γ (arr B (cst ()) _)          s β k _

-- The globe of a variable is a point at its own dimension.
point-dim : ∀ x β k → bd β k (lt (x ∷ []) []) ≡ lt (x ∷ []) []
point-dim x false zero    = refl
point-dim x true  zero    = refl
point-dim x false (suc k) = refl
point-dim x true  (suc k) = refl

wrapT-dim : ∀ Γ A x β k → TyIn Γ A →
            bd β (dim A + k) (wrapT A (lt (x ∷ []) [])) ≡ wrapT A (lt (x ∷ []) [])
wrapT-dim Γ A x β k t = trans (wrapT-bd Γ A _ β k t) (cong (wrapT A) (point-dim x β k))

-- The dim B boundaries of the globe of x : a → b over B are the
-- globes of a and b.
wrapT-ends : ∀ Γ B a b s → TyIn Γ B →
  (bd false (dim B) (wrapT (arr B (var a) (var b)) s) ≡ wrapT B (lt (a ∷ []) []))
  × (bd true (dim B) (wrapT (arr B (var a) (var b)) s) ≡ wrapT B (lt (b ∷ []) []))
wrapT-ends Γ B a b s t =
  trans (cong (λ k → bd false k w) (sym (+0 (dim B)))) (wrapT-bd Γ B l false 0 t) ,
  trans (cong (λ k → bd true k w) (sym (+0 (dim B)))) (wrapT-bd Γ B l true 0 t)
  where
  l = lt (a ∷ b ∷ []) (s ∷ [])
  w = wrapT B l
  +0 : ∀ a → a + 0 ≡ a
  +0 zero    = refl
  +0 (suc a) = cong suc (+0 a)

-- Labels: the variables of A, and those of s.
wrapT-mem : ∀ Γ A s y → TyIn Γ A → mem y (wrapT A s) ≡ (memL y (fvTy A) ∨ mem y s)
wrapT-mem Γ ⋆                       s y _ = refl
wrapT-mem Γ (arr B (var a) (var b)) s y (_ , _ , _ , _ , t) =
  trans (wrapT-mem Γ B _ y t)
  (trans (shuffle (memL y (fvTy B)) (y ==ℕ a) (y ==ℕ b) (mem y s))
         (cong (_∨ mem y s) (sym (memL-++ (fvTy B) (a ∷ b ∷ [])))))
  where
  memL-++ : ∀ xs ys → memL y (xs ++ ys) ≡ (memL y xs ∨ memL y ys)
  memL-++ []       ys = refl
  memL-++ (x ∷ xs) ys =
    trans (cong ((y ==ℕ x) ∨_) (memL-++ xs ys)) (sym (∨-assoc (y ==ℕ x) (memL y xs) (memL y ys)))
  shuffle : ∀ F p q m → (F ∨ ((p ∨ (q ∨ false)) ∨ (m ∨ false))) ≡ ((F ∨ (p ∨ (q ∨ false))) ∨ m)
  shuffle true  p     q     m = refl
  shuffle false true  q     m = refl
  shuffle false false true  m = refl
  shuffle false false false true  = refl
  shuffle false false false false = refl
wrapT-mem Γ (arr B (var a) (coh _ _ _)) s y ()
wrapT-mem Γ (arr B (var a) (cst ()))    s y _
wrapT-mem Γ (arr B (coh _ _ _) _)       s y ()
wrapT-mem Γ (arr B (cst ()) _)          s y _

------------------------------------------------------------------------
-- The globe of a variable is a diagram of Γ.

private
  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

cellOf : ∀ Γ o A → lookup Γ o ≡ just A → TyIn Γ A → Cell Γ (dim A) (parOf A) o
cellOf Γ o ⋆                       e _ = (⋆ , e) , dimOf-just Γ o ⋆ e
cellOf Γ o (arr B (var p) (var q)) e _ = (B , e) , dimOf-just Γ o _ e
cellOf Γ o (arr B (var p) (coh _ _ _)) e ()
cellOf Γ o (arr B (var p) (cst ()))    e _
cellOf Γ o (arr B (coh _ _ _) _)       e ()
cellOf Γ o (arr B (cst ()) _)          e _

wrapT-ex : ∀ Γ A s → TyIn Γ A → Ex Γ (dim A) (parOf A) s → Ex Γ 0 nothing (wrapT A s)
wrapT-ex Γ ⋆                       s _ x = x
wrapT-ex Γ (arr B (var a) (var b)) s (_ , _ , ea , eb , t) x =
  wrapT-ex Γ B _ t ((cellOf Γ a B ea t , cellOf Γ b B eb t , tt) , (x , tt))
wrapT-ex Γ (arr B (var a) (coh _ _ _)) s ()
wrapT-ex Γ (arr B (var a) (cst ()))    s _
wrapT-ex Γ (arr B (coh _ _ _) _)       s ()
wrapT-ex Γ (arr B (cst ()) _)          s _

point-ex : ∀ Γ x A → lookup Γ x ≡ just A → TyIn Γ A → Ex Γ (dim A) (parOf A) (lt (x ∷ []) [])
point-ex Γ x A e t = (cellOf Γ x A e t , tt) , tt
