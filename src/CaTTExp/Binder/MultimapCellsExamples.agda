------------------------------------------------------------------------
-- Examples for cells between unary multimaps as kernel cells
-- (CaTTExp.Binder.MultimapCells), checked by the certified checker
-- with plain CaTT's side condition and rule (MARK). Every statement is
-- `refl`.
--
--  * Currying as an operation: the canonical head `curry` on
--    (A, B, C, f) is curry(f) : B → A\C, and the same head on
--    (A, B, C, g) is curry(g).
--  * Currying a 2-cell: from a kernel 2-cell β : f ⇒ g between maps
--    A ⊗ B → C, the directed cut (GB-dcut) of the left-evaluation row
--    at k = 1, gap 1, gives a kernel 2-cell curry(f) ⇒ curry(g), whose
--    boundaries are exactly the curry head on f and on g
--    (`curry-boundary`).
--  * Its collars are the n = 0 comparison cells ε_f, ε_g of (GB-cut),
--    which are binary-multimap cells and so not kernel cells
--    themselves; they enter only inside the biclosed term.
--  * Rejections: non-canonical heads (an unused entry; an unused
--    atom), each otherwise well typed; a cell at gap 0 (oplax, not a
--    kernel cell); β not a 2-cell from f to g.
--  * The sort check: an instance that infers but sends the template's
--    data variable to a representable is not sorted (`unsorted`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.Multimap using (MMI; mmi)
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (extend)
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT
open import CaTTExp.Binder.Multimap using (sortedT)

module CaTTExp.Binder.MultimapCellsExamples where

𝕊 : Signature
𝕊 = extend P.∅ (cellBinders P.K)

open Signature 𝕊
open GCInterface K using (_⊗ᵗ_; _\\ᵗ_; mmcApp)
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

φ : List GB.Fm
φ = o0 ∷ o1 ∷ o2 ∷ []

-- The maps A ⊗ B → C.
F : GB.CTy
F = GB.op (((o0 GB.⊗ o1) ∷ []) GB.▸ o2)

evL : GB.Row
evL = GB.evLR (o1 ∷ []) o0 o2

-- f ∘ m, and curry(f) and ε_f at n = 0, for f the context variable i.
fm : Nat → GB.Tm
fm i = GB.comp (GB.var i) (GB.mP o0 o1 ∷ [])

curryT ε-T : Nat → GB.Tm
curryT i = GB.here (GB.tmpl evL 1 GB.inv 0) GB.gc φ (fm i ∷ [])
ε-T    i = GB.here (GB.tmpl evL 1 GB.inv 0) GB.gε φ (fm i ∷ [])

-- The canonical curry head.
curry : MMI
curry = mmi 3 (F ∷ []) (curryT 0)

------------------------------------------------------------------------
-- Context: A B C : ⋆, f g : A ⊗ B → C, β : f ⇒ g.

Γβ : Ctx
Γβ = ε ▸ ⋆ ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (a ⊗ᵗ b) c ▸ arr ⋆ (a ⊗ᵗ b) c
       ▸ arr (arr ⋆ (a ⊗ᵗ b) c) (v 3) (v 4)

curry-on : Tm → Tm
curry-on h = mmcApp curry (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ h)

curry-ty : (inferTy Γβ (curry-on (v 3)) ∷ inferTy Γβ (curry-on (v 4)) ∷ [])
         ≡ (just (arr ⋆ b (a \\ᵗ c)) ∷ just (arr ⋆ b (a \\ᵗ c)) ∷ [])
curry-ty = refl

-- Φ for the curried cell: f, g, β (at gap 1: a kernel 2-cell).
Φβ : GB.Ctx
Φβ = F ∷ F ∷ GB.hom GB.dir 1 F (GB.var 0) (GB.var 1) ∷ []

-- d of (GB-dcut) for the left-evaluation row, k = 1, gap 1.
curryCell : GB.Tm
curryCell = GB.here (GB.tmpl evL 1 GB.dir 1) GB.gc φ
  ( curryT 0 ∷ curryT 1 ∷ fm 0 ∷ fm 1 ∷ ε-T 0 ∷ ε-T 1
  ∷ GB.comp (GB.var 2) (GB.mP o0 o1 ∷ []) ∷ [])

argsβ : Sub
argsβ = ⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 3 ,ₛ v 4 ,ₛ v 5

-- The curried 2-cell, with boundaries the curry head on f and on g.
curry-boundary : inferTy Γβ (mmcApp (mmi 3 Φβ curryCell) argsβ)
               ≡ just (arr (arr ⋆ b (a \\ᵗ c)) (curry-on (v 3)) (curry-on (v 4)))
curry-boundary = refl

curry-cell-wf : wellTyped Γβ (mmcApp (mmi 3 Φβ curryCell) argsβ) ≡ true
curry-cell-wf = refl

------------------------------------------------------------------------
-- Rejections.

Φβ0 : GB.Ctx
Φβ0 = F ∷ F ∷ GB.hom GB.dir 0 F (GB.var 0) (GB.var 1) ∷ []

curryCell0 : GB.Tm
curryCell0 = GB.here (GB.tmpl evL 0 GB.dir 1) GB.gc φ
  ( curryT 0 ∷ curryT 1 ∷ fm 0 ∷ fm 1 ∷ ε-T 0 ∷ ε-T 1
  ∷ GB.comp (GB.var 2) (GB.mP o0 o1 ∷ []) ∷ [])

rejected : ( is-just (infer Γβ (mmcApp (mmi 3 (F ∷ F ∷ []) (curryT 1)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 3 ,ₛ v 4)))   -- unused entry 0
           ∷ is-just (infer Γβ (mmcApp (mmi 4 (F ∷ []) (curryT 0)) (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ a ,ₛ v 3)))  -- unused atom 3
           ∷ is-just (infer Γβ (mmcApp (mmi 3 Φβ0 curryCell0) argsβ))                                -- gap 0: not a kernel cell
           ∷ is-just (infer Γβ (mmcApp (mmi 3 Φβ curryCell) (⟨⟩ ,ₛ a ,ₛ b ,ₛ c ,ₛ v 4 ,ₛ v 3 ,ₛ v 5)))  -- β is not g ⇒ f
           ∷ [])
         ≡ (false ∷ false ∷ false ∷ false ∷ [])
rejected = refl

------------------------------------------------------------------------
-- Conservativity over plain CaTT (no constants).

open import CaTTExp.Binder.Embed using (module CaTT)
open CaTT P.∅ (cellBinders P.K) using (tm-iff; ctx-iff; ty-iff; sub-iff) public

------------------------------------------------------------------------
-- The sort check (`Multimap.sortedT`). The same curry instance with the
-- template's data variable sent to the representable ⟦D⁰⟧ infers (it is
-- an AdmI instance) but is not a kernel instance (KInst): the check
-- rejects it, so no mm or mmc head is built on it.

r0 : GB.Fm
r0 = GB.rep (GB.disk 0)

Fr : GB.CTy
Fr = GB.op (((o0 GB.⊗ o1) ∷ []) GB.▸ r0)

unsortedT : GB.Tm
unsortedT = GB.here (GB.tmpl evL 1 GB.inv 0) GB.gc (o0 ∷ o1 ∷ r0 ∷ []) (fm 0 ∷ [])

unsorted : is-just (GT.infer (Fr ∷ []) unsortedT) ∷ sortedT 2 unsortedT ∷ [] ≡ true ∷ false ∷ []
unsorted = refl
