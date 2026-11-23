------------------------------------------------------------------------
-- Examples for unary multimaps as kernel 1-cells
-- (CaTTExp.Binder.Multimap), checked by the certified checker with
-- plain CaTT's side condition and rule (MARK). Every statement is
-- `refl`.
--
--  * Currying: from f : A ⊗ B → C, the left-evaluation row at n = 0
--    (c of (GB-cut)) gives curry(f) : B → A\C; the right row gives
--    A → C/B.
--  * Uncurrying: from g : B → A\C, the binary multimap e^ℓ ∘ (1_A, g)
--    : (A, B ▸ C) is not a kernel 1-cell, but c of the pair row at
--    n = 0 turns it into the kernel 1-cell A ⊗ B → C.
--  * Identities and composites of kernel 1-cells as unary multimaps.
--  * Rejections: a binary result; a binary entry of Φ; an atom out of
--    range; ill-typed kernel arguments; a 2-cell for a 1-cell argument.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.Multimap
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
import CaTTExp.Gray.Biclosed.Syntax as GB

module CaTTExp.Binder.MultimapExamples where

𝕊 : Signature
𝕊 = extend P.∅ (multimapBinders P.K)

open Signature 𝕊
open GMInterface K using (_⊗ᵗ_; _\\ᵗ_; _//ᵗ_; mmApp)
open import CaTTExp.Binder.Typing 𝕊
open import CaTTExp.Binder.CheckWith 𝕊 cattSide varMark

inferTy : Ctx → Tm → Maybe Ty
inferTy Γ t = infer Γ t >>= λ r → just (fst r)

wellTyped : Ctx → Tm → Bool
wellTyped Γ t with ctx? Γ | inferTy Γ t
... | just w | just A = is-just (checkTy (sizeTy A) Γ w A)
... | _      | _      = false

v : Nat → Tm
v = var

a b c : Tm
a = v 0
b = v 1
c = v 2

o0 o1 o2 : GB.Fm
o0 = GB.obj 0
o1 = GB.obj 1
o2 = GB.obj 2

------------------------------------------------------------------------
-- Currying f : A ⊗ B → C.

Γf : Ctx
Γf = ε ▸ ⋆ ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (a ⊗ᵗ b) c

Φf : GB.Ctx
Φf = GB.op (((o0 GB.⊗ o1) ∷ []) GB.▸ o2) ∷ []

-- f ∘ m_{A,B} : (A, B ▸ C)
fm : GB.Tm
fm = GB.comp (GB.var 0) (GB.mP o0 o1 ∷ [])

-- c of the left-evaluation row (Φ = B), n = 0: (B ▸ A\C).
curryL : GB.Tm
curryL = GB.here (GB.tmpl (GB.evLR (o1 ∷ []) o0 o2) 1 GB.inv 0) GB.gc (o0 ∷ o1 ∷ o2 ∷ []) (fm ∷ [])

-- c of the right-evaluation row (Φ = A, bound object B), n = 0: (A ▸ C/B).
curryR : GB.Tm
curryR = GB.here (GB.tmpl (GB.evRR (o0 ∷ []) o1 o2) 1 GB.inv 0) GB.gc (o0 ∷ o1 ∷ o2 ∷ []) (fm ∷ [])

args-f : Sub
args-f = ⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 3

curryL-ty : inferTy Γf (mmApp (mmi 3 Φf curryL) args-f) ≡ just (arr ⋆ b (a \\ᵗ c))
curryL-ty = refl

curryR-ty : inferTy Γf (mmApp (mmi 3 Φf curryR) args-f) ≡ just (arr ⋆ a (c //ᵗ b))
curryR-ty = refl

curry-wf : (wellTyped Γf (mmApp (mmi 3 Φf curryL) args-f) ∷ wellTyped Γf (mmApp (mmi 3 Φf curryR) args-f) ∷ [])
         ≡ (true ∷ true ∷ [])
curry-wf = refl

------------------------------------------------------------------------
-- Uncurrying g : B → A\C: e^ℓ ∘ (1_A, g) : (A, B ▸ C), then c of the
-- pair row (L = R = [], U = A, V = B): (A ⊗ B ▸ C).

Γg : Ctx
Γg = ε ▸ ⋆ ▸ ⋆ ▸ ⋆ ▸ arr ⋆ b (a \\ᵗ c)

Φg : GB.Ctx
Φg = GB.op ((o1 ∷ []) GB.▸ (o0 GB.\\ o2)) ∷ []

evg : GB.Tm
evg = GB.comp (GB.eL o0 o2) (GB.idt o0 ∷ GB.var 0 ∷ [])

uncurry : GB.Tm
uncurry = GB.here (GB.tmpl (GB.pairR [] o0 o1 [] o2) 1 GB.inv 0) GB.gc (o0 ∷ o1 ∷ o2 ∷ []) (evg ∷ [])

uncurry-ty : inferTy Γg (mmApp (mmi 3 Φg uncurry) (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 3)) ≡ just (arr ⋆ (a ⊗ᵗ b) c)
uncurry-ty = refl

------------------------------------------------------------------------
-- Identity and composite of kernel 1-cells p : A → B, q : B → C.

Γpq : Ctx
Γpq = ε ▸ ⋆ ▸ ⋆ ▸ ⋆ ▸ arr ⋆ a b ▸ arr ⋆ b c

Φpq : GB.Ctx
Φpq = GB.op ((o0 ∷ []) GB.▸ o1) ∷ GB.op ((o1 ∷ []) GB.▸ o2) ∷ []

args-pq : Sub
args-pq = ⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 3 ,ₛ v 4

comp-ty : inferTy Γpq (mmApp (mmi 3 Φpq (GB.comp (GB.var 1) (GB.var 0 ∷ []))) args-pq) ≡ just (arr ⋆ a c)
comp-ty = refl

id-ty : inferTy Γpq (mmApp (mmi 3 Φpq (GB.idt (o0 GB.⊗ o2))) args-pq) ≡ just (arr ⋆ (a ⊗ᵗ c) (a ⊗ᵗ c))
id-ty = refl

------------------------------------------------------------------------
-- Rejections.

rejected : ( is-just (infer Γf (mmApp (mmi 3 Φf fm) args-f))                    -- binary result
           ∷ is-just (infer Γf (mmApp (mmi 3 (GB.op ((o0 ∷ o1 ∷ []) GB.▸ o2) ∷ []) (GB.var 0)) args-f))  -- binary entry
           ∷ is-just (infer Γf (mmApp (mmi 2 Φf curryL) (⟨⟩ ,ₛ a ,ₛ b ,ₛ v 3)))  -- atom 2 out of range
           ∷ is-just (infer Γf (mmApp (mmi 3 Φf curryL) (⟨⟩ ,ₛ b ,ₛ a ,ₛ c ,ₛ v 3)))  -- f is not B ⊗ A → C
           ∷ is-just (infer Γf (mmApp (mmi 3 Φf curryL) (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ a)))    -- an object for f
           ∷ is-just (infer Γpq (mmApp (mmi 3 Φpq (GB.comp (GB.var 0) (GB.var 1 ∷ []))) args-pq))  -- p ∘ q ill-typed
           ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ [])
rejected = refl

------------------------------------------------------------------------
-- Conservativity over plain CaTT (no constants).

open import CaTTExp.Binder.Embed using (module CaTT)
open CaTT P.∅ (multimapBinders P.K) using (tm-iff; ctx-iff; ty-iff; sub-iff) public
