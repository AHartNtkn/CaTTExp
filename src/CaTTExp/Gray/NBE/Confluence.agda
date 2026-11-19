------------------------------------------------------------------------
-- Local confluence of N/β/η by critical pairs, and confluence by
-- Newman's lemma (D18, §1.4 of the 2026-11-19 answer).
--
-- The overlaps handled below are the seven rows of the paper table
-- (both orientations), plus the variable and disjoint cases:
--
--   row 1  N/N                          N vs skip N
--   row 2  N/β, shared curry            N vs skip β
--   row 3  N/β, shared evaluation       β vs skip N
--   row 4  N/η, η-curry on the right    N vs skip η
--   row 5  N/η, η-curry on the left     N vs η
--   row 6  β/η, shared curry            β vs η
--   row 7  β/η, β uses η's evaluation   η vs body (β inside)
--
-- Everything is untyped: no typing hypothesis is used.
------------------------------------------------------------------------
module CaTTExp.Gray.NBE.Confluence (Fac G : Set) where

open import CaTTExp.Gray.NBE.Base
open import CaTTExp.Gray.NBE.Syntax Fac G
open import CaTTExp.Gray.NBE.Lemmas Fac G
open import CaTTExp.Gray.NBE.Termination Fac G using (sn)

Join : Word → Word → Set
Join v1 v2 = Σ Word λ w → (v1 ⟶* w) × (v2 ⟶* w)

swapJ : ∀ {v1 v2} → Join v1 v2 → Join v2 v1
swapJ (w , p , q) = w , q , p

joinEq : ∀ {v1 v2} → v1 ≡ v2 → Join v1 v2
joinEq {v1} e = v1 , ε , ≡* (sym e)

------------------------------------------------------------------------
-- A head N or β step against any other step

lcN : ∀ {DL DR CL CR D0L D0R q d A Z b w v2}
  → (e : DL ≡ CL ++ D0L) (f : DR ≡ D0R ++ CR)
  → tri DL q DR ∷ tri CL (cur d A Z b) CR ∷ w ⟶ v2
  → Join (tri CL (cur d A Z (wrap d A (tri D0L q D0R) ∷ b)) CR ∷ w) v2
-- N/N at the same position: D₀ is unique by cancellation.
lcN {CL = CL} {D0R = D0R} refl refl (N {D0R = D0R'} e f)
  with ++-cancelˡ CL e | ++-cancelʳ D0R D0R' f
... | refl | refl = joinEq refl
-- row 5: N/η, η-curry on the left
lcN {CL = CL} {CR = CR} {D0L = D0L} {D0R = D0R} {d = d} {A = A} {b = b} {w = w} refl refl
     (η {d = d0} {A = A0} {Z = Z0} {g = g} refl) =
  _ ,
  body (step≡ (η refl)
    (cong (_++ b) (sym (map-inCtx-∘ (pre d A) (post d A) D0L D0R g)))) ◅ ε ,
  ≡* (cong (_++ _) (sym (map-inCtx-∘ CL CR D0L D0R g)))
    ◅◅ N* (map (inCtx D0L D0R) g)
-- row 1: N/N
lcN {D0L = D0L} {D0R = D0R} refl refl
     (skip (N {CL = EL} {CR = ER} {D0L = C0L} {D0R = C0R} {d = d'} {A = A'} refl refl)) =
  _ ,
  one (N refl refl) ,
  N (++-assoc EL C0L D0L) (sym (++-assoc D0R C0R ER))
    ◅ one (body (N (sym (++-assoc (pre d' A') C0L D0L)) (++-assoc D0R C0R (post d' A'))))
-- row 2: N/β, shared curry
lcN {D0L = D0L} {D0R = D0R} {q = q} refl refl
     (skip (β {CL = EL} {CR = ER} {d = d} {A = A} {b = b} {w = w} refl refl)) =
  _ ,
  one (step≡ (β refl refl)
    (cong (λ t → t ∷ map (inCtx EL ER) b ++ w)
      (cong₂ (λ x y → tri x q y) (sym (++-assoc EL (pre d A) D0L))
                                 (++-assoc D0R (post d A) ER)))) ,
  ε
-- row 4: N/η, η-curry on the right
lcN refl refl (skip (η refl)) = _ , one (η refl) , ε
-- disjoint and variable cases
lcN refl refl (skip (skip s)) = _ , one (skip s) , one (N refl refl)
lcN refl refl (skip (body s)) = _ , one (body (skip s)) , one (N refl refl)
lcN refl refl (body s)        = _ , one (body (body s)) , one (N refl refl)

lcβ : ∀ {l r CL CR d A Z b w v2}
  → (e : l ≡ CL ++ pre d A) (f : r ≡ post d A ++ CR)
  → tri l (cur d A Z b) r ∷ tri CL (ev d A Z) CR ∷ w ⟶ v2
  → Join (map (inCtx CL CR) b ++ w) v2
-- β/β at the same position
lcβ _ _ (β _ _) = joinEq refl
-- row 6: β/η, shared curry
lcβ {CL = CL} {CR = CR} {d = d} {A = A} {Z = Z} {w = w} refl refl (η {g = g} refl) =
  joinEq (trans (cong (_++ w) (map-++ (inCtx CL CR) (map (wrap d A) g) (evT d A Z ∷ [])))
         (trans (++-assoc (map (inCtx CL CR) (map (wrap d A) g)) (inCtx CL CR (evT d A Z) ∷ []) w)
                (cong₂ _++_ (map-inCtx-∘ CL CR (pre d A) (post d A) g)
                            (cong (λ x → tri x (ev d A Z) CR ∷ w) (++-identityʳ CL)))))
-- row 3: N/β, shared evaluation
lcβ {d = d} {A = A} {Z = Z} {b = f} refl refl
     (skip (N {CL = CL} {CR = CR} {D0L = D0L} {D0R = D0R} {d = d'} {A = A'} {b = g} {w = w} refl refl)) =
  _ ,
  ≡* (cong (_++ _) (sym (map-inCtx-∘ CL CR D0L D0R f)))
    ◅◅ (N* (map (inCtx D0L D0R) f)
    ◅◅ ≡* (cong (λ x → tri CL (cur d' A' _ (x ++ g)) CR ∷ w)
             (map-inCtx-∘ (pre d' A') (post d' A') D0L D0R f))) ,
  N (++-assoc CL D0L (pre d A)) (sym (++-assoc (post d A) D0R CR))
    ◅ one (body (β (sym (++-assoc (pre d' A') D0L (pre d A)))
                   (++-assoc (post d A) D0R (post d' A'))))
lcβ refl refl (skip (skip s)) = _ , one (pre⟶ (map _ _) s) , one (β refl refl)
lcβ {CL = CL} {CR = CR} {w = w} refl refl (body s) =
  _ , one (suf⟶ w (ctx⟶ CL CR s)) , one (β refl refl)

------------------------------------------------------------------------
-- A head η step against any other step

lcη : ∀ {CL CR d A Z b g w v2}
  → (p : b ≡ map (wrap d A) g ++ (evT d A Z ∷ []))
  → tri CL (cur d A Z b) CR ∷ w ⟶ v2
  → Join (map (inCtx CL CR) g ++ w) v2
lcη p (N e f) = swapJ (lcN e f (η p))
lcη p (β e f) = swapJ (lcβ e f (η p))
-- η/η: the decomposition T_a[g] ; e_a is unique.
lcη {CL = CL} {CR = CR} {d = d} {A = A} {Z = Z} {g = g} {w = w} p (η {g = g'} p') =
  joinEq (cong (λ x → map (inCtx CL CR) x ++ w)
    (map-inj (wrap d A) (inCtx-inj (pre d A) (post d A)) g g'
      (++-cancelʳ (map (wrap d A) g) (map (wrap d A) g') (trans (sym p) p'))))
lcη {CL = CL} {CR = CR} {g = g} refl (skip s) =
  _ , one (pre⟶ (map (inCtx CL CR) g) s) , one (η refl)
-- η against a step inside its own body: either a step inside g
-- (variable case), or row 7, β consuming η's final evaluation.
lcη {CL = CL} {CR = CR} {d = d} {A = A} {Z = Z} {g = g} {w = w} refl (body s)
  with ev-split (map (wrap d A) g) s
... | before xs' s' e with ctx-refl (pre d A) (post d A) g s'
...   | g' , sg , e2 =
  _ , one (suf⟶ w (ctx⟶ CL CR sg)) ,
  one (η (trans e (cong (_++ (evT d A Z ∷ [])) e2)))
lcη {CL = CL} {CR = CR} {d = d} {A = A} {Z = Z} {g = g} {w = w} refl (body s)
  | beta xs0 f l r e1 el er e4 with map-snoc (wrap d A) g xs0 _ e1
... | g0 , t , eg , ex , et =
  _ ,
  (≡* eqv1 ◅◅ N* g0) ,
  ≡* (cong (λ x → tri CL (cur d A Z x) CR ∷ w)
        (trans e4 (cong₂ _++_ ex
          (trans (++-identityʳ (map (inCtx [] []) f)) (map-id inCtx-[] f)))))
  where
    t≡ : t ≡ tri [] (cur d A Z f) []
    t≡ = inCtx-inj (pre d A) (post d A)
           (trans et (cong₂ (λ x y → tri x (cur d A Z f) y)
                            (trans el (sym (++-identityʳ (pre d A))))
                            (trans er (++-identityʳ (post d A)))))
    eqv1 : map (inCtx CL CR) g ++ w
         ≡ map (inCtx CL CR) g0 ++ (tri CL (cur d A Z f) CR ∷ w)
    eqv1 =
      trans (cong (λ x → map (inCtx CL CR) x ++ w)
                  (trans eg (cong (λ x → g0 ++ (x ∷ [])) t≡)))
     (trans (cong (_++ w) (map-++ (inCtx CL CR) g0 (tri [] (cur d A Z f) [] ∷ [])))
     (trans (++-assoc (map (inCtx CL CR) g0) (inCtx CL CR (tri [] (cur d A Z f) []) ∷ []) w)
            (cong (λ x → map (inCtx CL CR) g0 ++ (tri x (cur d A Z f) CR ∷ w))
                  (++-identityʳ CL))))

------------------------------------------------------------------------
-- Local confluence

local-confluence : ∀ {u v1 v2} → u ⟶ v1 → u ⟶ v2 → Join v1 v2
local-confluence (N e f) s = lcN e f s
local-confluence (β e f) s = lcβ e f s
local-confluence (η p)   s = lcη p s
local-confluence (skip s) (N e f) = swapJ (lcN e f (skip s))
local-confluence (skip s) (β e f) = swapJ (lcβ e f (skip s))
local-confluence (skip s) (η p)   = swapJ (lcη p (skip s))
local-confluence (skip s) (skip s') with local-confluence s s'
... | _ , p , q = _ , skip* p , skip* q
local-confluence (skip s) (body s') = _ , one (body s') , one (skip s)
local-confluence (body s) (N e f) = swapJ (lcN e f (body s))
local-confluence (body s) (β e f) = swapJ (lcβ e f (body s))
local-confluence (body s) (η p)   = swapJ (lcη p (body s))
local-confluence (body s) (skip s') = _ , one (skip s') , one (body s)
local-confluence (body s) (body s') with local-confluence s s'
... | _ , p , q = _ , body* p , body* q

------------------------------------------------------------------------
-- Newman's lemma, and confluence

newman : ∀ u → SN u → ∀ {v1 v2} → u ⟶* v1 → u ⟶* v2 → Join v1 v2
newman u _ ε q = _ , q , ε
newman u _ (s ◅ p) ε = _ , ε , s ◅ p
newman u (acc r) (s1 ◅ p1) (s2 ◅ p2) with local-confluence s1 s2
... | w , q1 , q2 with newman _ (r _ s1) p1 q1
...   | x , a1 , a2 with newman _ (r _ s2) p2 (q2 ◅◅ a2)
...     | y , b1 , b2 = y , a1 ◅◅ b2 , b1

confluence : ∀ {u v1 v2} → u ⟶* v1 → u ⟶* v2 → Join v1 v2
confluence {u} = newman u (sn u)

-- Normal forms are unique.
Normal : Word → Set
Normal w = ∀ {v} → w ⟶ v → ⊥

normal-stuck : ∀ {n v} → Normal n → n ⟶* v → n ≡ v
normal-stuck nf ε       = refl
normal-stuck nf (s ◅ _) = ⊥-elim (nf s)

unique-normal-form : ∀ {u n1 n2} → u ⟶* n1 → u ⟶* n2
  → Normal n1 → Normal n2 → n1 ≡ n2
unique-normal-form p q nf1 nf2 with confluence p q
... | w , a , b = trans (normal-stuck nf1 a) (sym (normal-stuck nf2 b))
